Require Import HoTT.
Require Export HoTT.

(*
Lemma 13 in paper
*)
Theorem apTransport (A B : Type0) (f g : A -> B) (e : f = g) (x y : A) (p : x = y) :
  transport (fun h => h x = h y) e (ap f p) = ap g p.
Proof.
induction e.
reflexivity.
Qed.

(*
Definition 6 in paper
*)
Definition fPath {A B : Type0} {f g : A -> B} (e : f = g) (x : A) : f x = g x.
Proof.
induction e.
reflexivity.
Defined.

(*
Lemma 14 in paper
*)
Theorem funTransport (A B : Type0) (f g : A -> B) (e : f = g) (x y : A) (p : f x = f y) :
  transport (fun h => h x = h y) e p = (fPath e x)^ @ p @ (fPath e y).
Proof.
induction e.
cbn.
rewrite concat_1p.
rewrite concat_p1.
reflexivity.
Qed.


Ltac reduceTransport :=
  rewrite @HoTT.Types.Paths.transport_paths_FlFr ;
  rewrite ap_compose.

(*
Colimits as higher inductive type
*)
Module Export Colims.

Private Inductive colim
  (F : nat -> Type0)
  (f : forall (n : nat), F n -> F(S n)) : Type0 :=
| inc : forall (n : nat), F n -> colim F f.

Axiom com : 
  forall 
    (F : nat -> Type0) 
    (f : forall (n : nat), F n -> F(S n))
    (n : nat) 
    (x : F n), 
  inc F f n x = inc F f (S n) (f n x).

(*
Recursion rule for colimit using Licata's trick
*)
Fixpoint colim_rec
  (P : Type)
  (F : nat -> Type0)
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
  (F : nat -> Type0)
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
  (F : nat -> Type0)
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
  (F : nat -> Type0)
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
Definition CC_A : forall (A : Type0),
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
Definition A_CC (A : Type0) (a : A) : colim (fun (_ : nat) => A) (fun (_ : nat) => idmap) :=
  inc (fun _ : nat => A) (fun n : nat => idmap) 1 a.

Definition iso_CC_A (A : Type0) (x : A) :
  CC_A A (A_CC A x) = x := reflexivity x.

Definition iso_A_CC : forall (A : Type0) (x : colim (fun (_ : nat) => A) (fun (_ : nat) => idmap)),
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
Definition Sum (G1 G2 : nat -> Type0) (n : nat) : Type0
  := sum (G1 n) (G2 n).

(*
The sum is a functor.
*)
Definition SMap 
  (G1 G2 : nat -> Type0)
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
  forall  (G1 G2 : nat -> Type0)
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
  forall  (G1 G2 : nat -> Type0)
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
  forall  (G1 G2 : nat -> Type0)
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
  forall  (G1 G2 : nat -> Type0)
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