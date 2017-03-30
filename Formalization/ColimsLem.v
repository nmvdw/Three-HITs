Require Import HoTT.
Require Export HoTT.
Require Import FunextAxiom.

(*
Lemma 13 in paper
*)
Definition apTransport (A B : Type0) (f g : A -> B) (e : f = g) (x y : A) (p : x = y) :
  transport (fun h => h x = h y) e (ap f p) = ap g p :=
match e with
  idpath => 1
end.

(*
Definition 6 in paper
*)
Definition fPath {A B : Type0} {f g : A -> B} (e : f = g) (x : A) : f x = g x :=
match e with
  idpath => 1
end.

(*
Lemma 14 in paper
*)
Definition funTransport (A B : Type0) (f g : A -> B) (e : f = g) (x y : A) (p : f x = f y) :
  transport (fun h => h x = h y) e p = (fPath e x)^ @ p @ (fPath e y) :=
match e with
  idpath => (concat_p1 p)^ @ (ap (fun q => q @ 1) (concat_1p p))^
end.

Ltac reduceTransport :=
  rewrite @HoTT.Types.Paths.transport_paths_FlFr ;
  rewrite ap_compose.

(*
Colimits as higher inductive type
*)
Module Export Colims.

Private Inductive colim
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n)) : Type :=
| inc : forall (n : nat), F n -> colim F f.

Axiom com : 
  forall 
    (F : nat -> Type) 
    (f : forall (n : nat), F n -> F(S n))
    (n : nat) 
    (x : F n), 
  inc F f n x = inc F f (S n) (f n x).

(*
Recursion rule for colimit using Licata's trick
*)
Fixpoint colim_rec
  (P : Type)
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (Pi : forall (n : nat), F n -> P)
  (Pc : forall (n : nat) (x : F n), Pi n x = Pi (S n) (f n x))
  (x : colim F f)
  {struct x}
  : P
  := 
    (match x return _ -> P with
      | inc n x => fun _ => Pi n x
    end) Pc.

Axiom colim_rec_beta_com : forall
  (P : Type)
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (Pi : forall (n : nat), F n -> P)
  (Pc : forall (n : nat) (x : F n), Pi n x = Pi (S n) (f n x))
  (n : nat)
  (x : F n)
  , ap (colim_rec P F f Pi Pc) (com F f n x) = Pc n x.

(*
Induction rule for colimit using Licata's trick
*)
Fixpoint colim_ind
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (P : colim F f -> Type)
  (Pi : forall (n : nat), forall (x : F n), P (inc F f n x))
  (Pc : forall (n : nat) (x : F n), (com F f n x) # Pi n x = Pi (S n) (f n x))
  (x : colim F f)
  {struct x}
  : P x
  := 
    (match x return _ -> P x with
      | inc n x => fun _ => Pi n x
    end) Pc.

Axiom colim_ind_beta_com : forall
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (P : colim F f -> Type)
  (Pi : forall (n : nat), forall (x : F n), P (inc F f n x))
  (Pc : forall (n : nat) (x : F n), (com F f n x) # Pi n x = Pi (S n) (f n x))
  (n : nat)
  (x : F n)
  , apD (colim_ind F f P Pi Pc) (com F f n x) = Pc n x.
End Colims.

(*
The colimit of F(X) = A is A.
Lemma 10 in paper.
*)
Section ColimConst.

(*
colim A id -> A
Defined by F(n) -> A as id.
*)
Definition CC_A : forall (A : Type),
  colim (fun (_ : nat) => A) (fun (_ : nat) => idmap) -> A.
Proof.
intro A.
refine (colim_rec _ _ _ _ _).
 Unshelve.
 Focus 2.
 intro n.
 apply idmap.

 intros.
 reflexivity.
Defined.

(*
A -> colim A id
Defined by inc 0
*)
Definition A_CC (A : Type) (a : A) : colim (fun (_ : nat) => A) (fun (_ : nat) => idmap) :=
  inc (fun _ : nat => A) (fun n : nat => idmap) 1 a.

Definition iso_CC_A (A : Type) (x : A) :
  CC_A A (A_CC A x) = x := reflexivity x.

Definition iso_A_CC : forall (A : Type) (x : colim (fun (_ : nat) => A) (fun (_ : nat) => idmap)),
  x = A_CC A (CC_A A x).
Proof.
intro A.
refine (colim_ind _ _ _ _ _).
 Unshelve.
 Focus 2.
 intros.
 induction n.
   apply com.
   apply ((com (fun _ : nat => A) (fun _ : nat => idmap) n x)^ @ IHn).

 intros.
 reduceTransport.
 rewrite ap_idmap.
 rewrite colim_rec_beta_com.
 rewrite concat_p1.
 induction n ; cbn.
 - reflexivity.
 - rewrite IHn.
   reflexivity.
Defined.

End ColimConst.

(*
Colimits commute with sums.
Lemma 11 in paper.
*)
Section ColimSum.

(*
Sum of two functors.
*)
Definition Sum (G1 G2 : nat -> Type) (n : nat) : Type
  := sum (G1 n) (G2 n).

(*
The sum is a functor.
*)
Definition SMap 
  (G1 G2 : nat -> Type)
  (g1 : forall (n : nat), G1 n -> G1 (S n))
  (g2 : forall (n : nat), G2 n -> G2 (S n))
  (n : nat)
  (x : Sum G1 G2 n)
  : Sum G1 G2 (S n) :=
match x with
  | inl x => inl (g1 n x)
  | inr y => inr (g2 n y)
end.

(*
colim (G1 + G2) -> colim G1 + colim G2
Defined by
  G1 n + G2 n
  For x : G1 n it is inl(inc n x)
  For y : G2 n it is inr(inc n y)
*)
Definition colim_S : 
  forall  (G1 G2 : nat -> Type)
          (g1 : forall (n : nat), G1 n -> G1 (S n))
          (g2 : forall (n : nat), G2 n -> G2 (S n)),
  colim (Sum G1 G2) (SMap G1 G2 g1 g2)
  ->
  sum
    (colim G1 g1)
    (colim G2 g2).
Proof.
intros G1 G2 g1 g2.
refine (colim_rec _ _ _ _ _).
Unshelve.
  Focus 2.
  compute.
  intros n i.
  destruct i as [x | y].
    Focus 1.
    left.
    apply (inc G1 g1 n x).

    right.
    apply (inc G2 g2 n y).

  intros n i.
  destruct i as [x | y].
    apply (ap inl (com G1 g1 n x)).

    apply (ap inr (com G2 g2 n y)).
Defined.


(*
colim (G1 F) + colim (G2 F) -> colim (G1 F + G2 F)
Defined by
  For x : G1(F n) it is inc n (inl x)
  For y : G2(F n) it is inc n (inr x)
*)
Definition S_colim : 
  forall  (G1 G2 : nat -> Type)
          (g1 : forall (n : nat), G1 n -> G1 (S n))
          (g2 : forall (n : nat), G2 n -> G2 (S n)),
  sum
    (colim G1 g1)
    (colim G2 g2)
  ->
  colim (Sum G1 G2) (SMap G1 G2 g1 g2).
Proof.
intros G1 G2 g1 g2 i.
destruct i as [x | y].
refine (colim_rec _ _ _ _ _ x).
Unshelve.
  Focus 3.
  intros n a.
  apply (inc (Sum G1 G2) (SMap G1 G2 g1 g2) n).
  left.
  apply a.

  intros n a.
  apply (com (Sum G1 G2) (SMap G1 G2 g1 g2) n (inl a)).

refine (colim_rec _ _ _ _ _ y).
Unshelve.
  Focus 2.
  intros n b.
  apply (inc (Sum G1 G2) (SMap G1 G2 g1 g2) n).
  right.
  apply b.

  cbn.
  intros n b.
  apply (com (Sum G1 G2) (SMap G1 G2 g1 g2) n (inr b)).
Defined.

Theorem S_iso_1 :
  forall  (G1 G2 : nat -> Type)
          (g1 : forall (n : nat), G1 n -> G1 (S n))
          (g2 : forall (n : nat), G2 n -> G2 (S n))
          (i : sum
              (colim G1 g1)
              (colim G2 g2)),
  colim_S G1 G2 g1 g2 (S_colim G1 G2 g1 g2 i) = i.
Proof.
intros G1 G2 g1 g2 i.
destruct i as [x| y].
 Focus 1.
 refine (colim_ind _ _ _ _ _ x).
  Unshelve.
  Focus 2.
  intro z.
  apply
   (colim_S G1 G2 g1 g2 (S_colim G1 G2 g1 g2 (inl z)) = inl z).

  Focus 2.
  intros n a.
  reflexivity.

  intros n a.
  reduceTransport.
  rewrite colim_rec_beta_com.
  rewrite colim_rec_beta_com.
  rewrite concat_p1.
  apply concat_Vp.

 refine (colim_ind _ _ _ _ _ y).
  Unshelve.
  Focus 2.
  intro z.
  apply
   (colim_S G1 G2 g1 g2 (S_colim G1 G2 g1 g2 (inr z)) = inr z).

  Focus 2.
  intros n a.
  reflexivity.

  intros n a.
  reduceTransport.
  rewrite colim_rec_beta_com.
  rewrite colim_rec_beta_com.
  rewrite concat_p1.
  apply concat_Vp.
Qed.

Theorem S_iso_2 :
  forall  (G1 G2 : nat -> Type)
          (g1 : forall (n : nat), G1 n -> G1 (S n))
          (g2 : forall (n : nat), G2 n -> G2 (S n))
          (i : colim (Sum G1 G2) (SMap G1 G2 g1 g2)),
  i = S_colim G1 G2 g1 g2 (colim_S G1 G2 g1 g2 i).
Proof.
intros G1 G2 g1 g2 i.
refine (colim_ind _ _ _ _ _ i).
 Unshelve.
 Focus 2.
 intro x.
 apply (x = S_colim G1 G2 g1 g2 (colim_S G1 G2 g1 g2 x)).

 Focus 2.
 intros.
 destruct x; reflexivity.

 intros.
 destruct x; cbn; reduceTransport; rewrite ap_idmap; rewrite concat_p1; rewrite colim_rec_beta_com.
  Focus 1.
  rewrite <- (ap_compose inl).
  rewrite colim_rec_beta_com.
  apply concat_Vp.

  rewrite <- (ap_compose inr).
  rewrite colim_rec_beta_com.
  apply concat_Vp.

Qed.

End ColimSum.

(*
Coequalizers as a higher inductive type
*)
Module Export Coeq.

Private Inductive coeq
  (A B : Type)
  (f g : A -> B) : Type :=
| inC : B -> coeq A B f g.

Axiom glue : 
  forall 
    (A B : Type) 
    (f g : A -> B)
    (x : A),
  inC A B f g (f x) = inC A B f g (g x).

(*
Recursion rule for coequalizer using Licata's trick
*)
Fixpoint coeq_rec
  (P : Type)
  (A B : Type) 
  (f g : A -> B)
  (Pi : B -> P)
  (Pg : forall (x : A), Pi (f x) = Pi (g x))
  (x : coeq A B f g)
  {struct x}
  : P
  := 
    (match x return _ -> P with
      | inC x => fun _ => Pi x
    end) Pg.

Axiom coeq_rec_beta_glue : forall
  (P : Type)
  (A B : Type) 
  (f g : A -> B)
  (Pi : B -> P)
  (Pg : forall (x : A), Pi (f x) = Pi (g x))
  (x : A)
  , ap (coeq_rec P A B f g Pi Pg) (glue A B f g x) = Pg x.

(*
Induction rule for colimit using Licata's trick
*)
Fixpoint coeq_ind
  (A B : Type) 
  (f g : A -> B)
  (P : coeq A B f g -> Type)
  (Pi : forall (x : B), P (inC A B f g x))
  (Pg : forall (x : A), (glue A B f g x) # Pi (f x) = Pi (g x))
  (x : coeq A B f g)
  {struct x}
  : P x
  := 
    (match x return _ -> P x with
      | inC x => fun _ => Pi x
    end) Pg.

Axiom coeq_ind_beta_glue : forall
  (A B : Type) 
  (f g : A -> B)
  (P : coeq A B f g -> Type)
  (Pi : forall (x : B), P (inC A B f g x))
  (Pg : forall (x : A), (glue A B f g x) # Pi (f x) = Pi (g x))
  (x : A)
  , apD (coeq_ind A B f g P Pi Pg) (glue A B f g x) = Pg x.
End Coeq.

(*
Colimits as coequalizers of sums
*)
Module Export ColimAsCoeq.

Parameter F : nat -> Type0.
Parameter f : forall (n : nat), F n -> F(n.+1).

Definition C1 : Type0 := sigT F.

Definition g1 : C1 -> C1 := idmap.

Definition g2 (x : C1) : C1 :=
match x with
  existT n y => existT F (n.+1) (f n y)
end.

Definition C : Type0 := coeq C1 C1 g1 g2.
Definition H : Type0 := colim F f.

Definition CToH : C -> H.
Proof.
refine (coeq_rec _ _ _ _ _ _ _).
 Unshelve.
 Focus 2.
 induction 1.
 apply (inc F f proj1_sig proj2_sig).

 intro x.
 induction x.
 apply com.
Defined.

Definition HToC : H -> C.
Proof.
refine (colim_rec _ _ _ _ _).
 Unshelve.
 Focus 2.
 intros.
 apply (inC C1 C1 g1 g2 (n;H0)).

 intros.
 cbn.
 apply (glue C1 C1 g1 g2).
Defined.

Theorem CToHEq :
  forall (x : C), HToC(CToH x) = x.
Proof.
refine (coeq_ind _ _ _ _ _ _ _).
 Unshelve.
 Focus 2.
 intros.
 reflexivity.

 intros.
 induction x.
 reduceTransport.
 rewrite ap_idmap.
 rewrite concat_p1.
 rewrite coeq_rec_beta_glue.
 rewrite colim_rec_beta_com.
 apply concat_Vp.
Defined.

Theorem HToCEq :
  forall (x : H), CToH(HToC x) = x.
Proof.
refine (colim_ind _ _ _ _ _).
 Unshelve.
 Focus 2.
 intros.
 reflexivity.

 intros.
 reduceTransport.
 rewrite ap_idmap.
 rewrite concat_p1.
 rewrite colim_rec_beta_com.
 rewrite (coeq_rec_beta_glue H C1 C1 g1 g2).
 apply concat_Vp.
Defined.

End ColimAsCoeq.