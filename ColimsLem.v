Require Import HoTT.
Require Export HoTT.

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

Lemma CC_A : forall (A : Type0),
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

Lemma A_CC : forall (A : Type0),
  A -> colim (fun (_ : nat) => A) (fun (_ : nat) => idmap).
Proof.
intros.
apply (inc (fun _ : nat => A) (fun n : nat => idmap) 1).
apply H.
Defined.

Lemma iso_CC_A : forall (A : Type0) (x : A),
  CC_A A (A_CC A x) = x.
Proof.
intros.
reflexivity.
Qed.

Lemma iso_A_CC : forall (A : Type0) (x : colim (fun (_ : nat) => A) (fun (_ : nat) => idmap)),
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
 rewrite @HoTT.Types.Paths.transport_paths_FlFr.
 rewrite ap_idmap.
 rewrite ap_compose.
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

Definition Sum (G1 : Type0 -> Type0) (G2 : Type0 -> Type0) (F : nat -> Type0) : nat -> Type0
  := fun (n : nat) => sum (G1 (F n)) (G2 (F n)).

Definition SMap 
  (G1 : Type0 -> Type0)
  (G2 : Type0 -> Type0)
  (G1F : forall (A B : Type0), (A -> B) -> G1 A -> G1 B)
  (G2F : forall (A B : Type0), (A -> B) -> G2 A -> G2 B)
  (F : nat -> Type0)
  (f : forall (n : nat), F n -> F (S n))
  : forall (n : nat), Sum G1 G2 F n -> Sum G1 G2 F (S n).
Proof.
compute.
intros.
destruct H as [x| y].
 left.
 apply (G1F (F n) (F (S n)) (f n) x).

 right.
 apply (G2F (F n) (F (S n)) (f n) y).
Defined.

Definition colim_S : 
  forall  (F : nat -> Type0)
          (f : forall (n : nat), F n -> F(S n))
          (G1 G2 : Type0 -> Type0)
          (G1F : forall (A B : Type0), (A -> B) -> G1 A -> G1 B)
          (G2F : forall (A B : Type0), (A -> B) -> G2 A -> G2 B),
  colim (Sum G1 G2 F) (SMap G1 G2 G1F G2F F f)
  ->
  sum
    (colim (fun (n : nat) => G1 (F n)) (fun (n : nat) => G1F (F n) (F (S n)) (f n)))
    (colim (fun (n : nat) => G2 (F n)) (fun (n : nat) => G2F (F n) (F (S n)) (f n))).
Proof.
intros F f G1 G2 G1F G2F.
refine (colim_rec _ _ _ _ _).
Unshelve.
  Focus 2.
  compute.
  intros n i.
  destruct i as [x | y].
    Focus 1.
    left.
    apply (inc (fun n0 : nat => G1 (F n0)) (fun n0 : nat => G1F (F n0) (F n0.+1) (f n0)) n x).

    right.
    apply (inc (fun n0 : nat => G2 (F n0)) (fun n0 : nat => G2F (F n0) (F n0.+1) (f n0)) n y).

  intros n i.
  destruct i as [x | y].
    Focus 1.
    apply (ap inl (com (fun n0 : nat => G1 (F n0)) (fun n0 : nat => G1F (F n0) (F n0.+1) (f n0)) n x)).

    apply (ap inr (com (fun n0 : nat => G2 (F n0)) (fun n0 : nat => G2F (F n0) (F n0.+1) (f n0)) n y)).
Defined.

Definition S_colim : 
  forall  (F : nat -> Type0)
          (f : forall (n : nat), F n -> F(S n))
          (G1 G2 : Type0 -> Type0)
          (G1F : forall (A B : Type0), (A -> B) -> G1 A -> G1 B)
          (G2F : forall (A B : Type0), (A -> B) -> G2 A -> G2 B),
  sum
    (colim (fun (n : nat) => G1 (F n)) (fun (n : nat) => G1F (F n) (F (S n)) (f n)))
    (colim (fun (n : nat) => G2 (F n)) (fun (n : nat) => G2F (F n) (F (S n)) (f n)))
  ->
  colim (Sum G1 G2 F) (SMap G1 G2 G1F G2F F f).
Proof.
intros F f G1 G2 G1F G2F i.
destruct i as [x | y].
refine (colim_rec _ _ _ _ _ x).
Unshelve.
  Focus 3.
  intros n a.
  apply (inc (Sum G1 G2 F) (SMap G1 G2 G1F G2F F f) n).
  left.
  apply a.

  intros n a.
  apply (com (Sum G1 G2 F) (SMap G1 G2 G1F G2F F f) n (inl a)).

refine (colim_rec _ _ _ _ _ y).
Unshelve.
  Focus 2.
  intros n b.
  apply (inc (Sum G1 G2 F) (SMap G1 G2 G1F G2F F f) n).
  right.
  apply b.

  cbn.
  intros n b.
  apply (com (Sum G1 G2 F) (SMap G1 G2 G1F G2F F f) n (inr b)).
Defined.

Theorem S_iso_1 :
  forall  (F : nat -> Type0)
          (f : forall (n : nat), F n -> F(S n))
          (G1 G2 : Type0 -> Type0)
          (G1F : forall (A B : Type0), (A -> B) -> G1 A -> G1 B)
          (G2F : forall (A B : Type0), (A -> B) -> G2 A -> G2 B)
          (i : sum
              (colim (fun (n : nat) => G1 (F n)) (fun (n : nat) => G1F (F n) (F (S n)) (f n)))
              (colim (fun (n : nat) => G2 (F n)) (fun (n : nat) => G2F (F n) (F (S n)) (f n)))),
  colim_S F f G1 G2 G1F G2F (S_colim F f G1 G2 G1F G2F i) = i.
Proof.
intros F f G1 G2 G1F G2F i.
destruct i as [x| y].
 Focus 1.
 refine (colim_ind _ _ _ _ _ x).
  Unshelve.
  Focus 2.
  intro z.
  apply
   (colim_S F f G1 G2 G1F G2F (S_colim F f G1 G2 G1F G2F (inl z)) = inl z).

  Focus 2.
  intros n a.
  reflexivity.

  intros n a.
  rewrite @HoTT.Types.Paths.transport_paths_FlFr.
  rewrite concat_p1.
  rewrite ap_compose.
  rewrite colim_rec_beta_com.
  rewrite colim_rec_beta_com.
  apply concat_Vp.

 refine (colim_ind _ _ _ _ _ y).
  Unshelve.
  Focus 2.
  intro z.
  apply
   (colim_S F f G1 G2 G1F G2F (S_colim F f G1 G2 G1F G2F (inr z)) = inr z).

  Focus 2.
  intros n a.
  reflexivity.

  intros n a.
  rewrite @HoTT.Types.Paths.transport_paths_FlFr.
  rewrite concat_p1.
  rewrite ap_compose.
  rewrite colim_rec_beta_com.
  rewrite colim_rec_beta_com.
  apply concat_Vp.
Qed.


Theorem S_iso_2 :
  forall  (F : nat -> Type0)
          (f : forall (n : nat), F n -> F(S n))
          (G1 G2 : Type0 -> Type0)
          (G1F : forall (A B : Type0), (A -> B) -> G1 A -> G1 B)
          (G2F : forall (A B : Type0), (A -> B) -> G2 A -> G2 B)
          (i : colim (Sum G1 G2 F) (SMap G1 G2 G1F G2F F f)),
  S_colim F f G1 G2 G1F G2F (colim_S F f G1 G2 G1F G2F i) = i.
Proof.
intros F f G1 G2 G1F G2F.
refine (colim_ind _ _ _ _ _).
  Unshelve.
  Focus 2.
  destruct x ; reflexivity.

  intros.
  destruct x ; cbn ;
    rewrite @HoTT.Types.Paths.transport_paths_FlFr ;
    rewrite ap_idmap ;
    rewrite concat_p1 ;
    rewrite ap_compose ;
    rewrite colim_rec_beta_com.
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
Colims commute with products.
Lemma 12 in paper.
 *)
Section ColimProd.

Definition P (G1 : Type0 -> Type0) (G2 : Type0 -> Type0) (F : nat -> Type0) : nat -> Type0
  := fun (n : nat) => prod (G1 (F n)) (G2 (F n)).

Definition PMap 
  (G1 : Type0 -> Type0)
  (G2 : Type0 -> Type0)
  (G1F : forall (A B : Type0), (A -> B) -> G1 A -> G1 B)
  (G2F : forall (A B : Type0), (A -> B) -> G2 A -> G2 B)
  (F : nat -> Type0)
  (f : forall (n : nat), F n -> F (S n))
  : forall (n : nat), P G1 G2 F n -> P G1 G2 F (S n).
Proof.
intros.
destruct H.
split.
 apply (G1F (F n) (F (S n)) (f n) fst).

 apply (G2F (F n) (F (S n)) (f n) snd).
Defined.

Definition colim_P : 
  forall  (F : nat -> Type0)
          (f : forall (n : nat), F n -> F(S n))
          (G1 G2 : Type0 -> Type0)
          (G1F : forall (A B : Type0), (A -> B) -> G1 A -> G1 B)
          (G2F : forall (A B : Type0), (A -> B) -> G2 A -> G2 B) ,
  colim (P G1 G2 F) (PMap G1 G2 G1F G2F F f)
  ->
  prod
    (colim (fun (n : nat) => G1 (F n)) (fun (n : nat) => G1F (F n) (F (S n)) (f n)))
    (colim (fun (n : nat) => G2 (F n)) (fun (n : nat) => G2F (F n) (F (S n)) (f n))).
Proof.
intros F f G1 G2 G1F G2F.
refine (colim_rec _ _ _ _ _).
 Unshelve.
 Focus 2.
 compute.
 intros.
 destruct H.
 split.
  apply
   (inc (fun n0 : nat => G1 (F n0))
      (fun n0 : nat => G1F (F n0) (F n0.+1) (f n0)) n fst).

  apply
   (inc (fun n0 : nat => G2 (F n0))
      (fun n0 : nat => G2F (F n0) (F n0.+1) (f n0)) n snd).

 compute.
 intros.
 destruct x.
 apply path_prod.
  Focus 1.
  apply com.

  apply com.
Defined.

Inductive leq : nat -> nat -> Type0 :=
| leqR : forall (n : nat), leq n n
| leqS : forall (n m : nat), leq n m -> leq n (S m).

Hint Constructors leq.

Lemma leqZ : forall n, leq 0 n.
Proof.
induction n; auto.
Defined.

Lemma leqSS : forall n m, leq n m -> leq (S n) (S m).
Proof.
induction 1 ; auto.
Defined.

Lemma leqSC : forall n m, leq n m -> m = n \/ leq (S n) m.
Proof.
intros.
induction H.
 left.
 reflexivity.

 destruct IHleq.
  right.
  apply (transport (fun (x : nat) => leq (x.+1) (m.+1)) p (leqR (m.+1))).

  right.
  apply leqS.
  apply l.
Defined.

Lemma leqTot : forall n m, leq n m + leq m n.
Proof.
intros.
induction n.
- left.
  apply leqZ.
- destruct IHn ; auto.
  destruct (leqSC n m l).
    * right.
      apply (transport (fun (x : nat) => leq m (x.+1)) p).
      apply leqS.
      apply leqR.
    * auto.
Defined.


Lemma help
  (F : nat -> Type0) 
  (f : forall (n : nat), F n -> F(n.+1)) 
  (G : Type0 -> Type0) 
  (GF : forall A B : Type0, (A -> B) -> G A -> G B)
  : (forall (x y : nat), leq x y -> G(F x) -> G(F y)).
Proof.
intros x y p.
induction p.
 apply idmap.

 intro x.
 apply (GF (F m) (F m.+1) (f m) (IHp x)).
Defined.

Definition P_colim : 
  forall  (F : nat -> Type0)
          (f : forall (n : nat), F n -> F(S n))
          (G1 G2 : Type0 -> Type0)
          (G1F : forall (A B : Type0), (A -> B) -> G1 A -> G1 B)
          (G2F : forall (A B : Type0), (A -> B) -> G2 A -> G2 B) ,
  prod
    (colim (fun (n : nat) => G1 (F n)) (fun (n : nat) => G1F (F n) (F (S n)) (f n)))
    (colim (fun (n : nat) => G2 (F n)) (fun (n : nat) => G2F (F n) (F (S n)) (f n)))
  ->
  colim (P G1 G2 F) (PMap G1 G2 G1F G2F F f).
Proof.
intros F f G1 G2 G1F G2F pair.
destruct pair.
refine (colim_rec _ _ _ _ _ fst).
Unshelve.
  Focus 2.
  intros n x.
  refine (colim_rec _ _ _ _ _ snd).
  Unshelve.
    Focus 2.
    intros m y.
    destruct (leqTot n m).
      apply (inc (P G1 G2 F) (PMap G1 G2 G1F G2F F f) m).
      apply (help F f G1 G1F n m l x, y).

      apply (inc (P G1 G2 F) (PMap G1 G2 G1F G2F F f) n).
      apply (x, help F f G2 G2F m n l y).

  cbn.
  intros m y.
  induction n.
    Focus 1.
    induction m ; apply com.

    induction m.
