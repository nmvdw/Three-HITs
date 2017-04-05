Require Import HoTT.
Require Import HoTT.HIT.Colimits.

(* Here we collect general facts about HITs in the HoTT library.
   We will then put the generally useful ones into the HoTT library. *)

(* Note: the coequalizers are already around, see
   http://hott.github.io/HoTT/proviola-html/HoTT.HIT.Colimits.Coequalizer.html *)

(* Note: the mapping telescope is already around, see
   https://ncatlab.org/nlab/show/mapping+telescope for naming,
   and http://hott.github.io/HoTT/proviola-html/HoTT.HIT.Colimits.MappingTelescope.html,
   although that file fails to actually define the relevant HIT, it just provides
   the graph for it. Perhaps we should re-define mapping telescopes directly, i.e.,
   just take the development from ColimsLem.v (that one should be broken down into
   seeral pieces.
*)

(* In order to nicely work with colimits over the natural numbers, we want to abbreviate some principles.
   These principles are closer to what was written in the paper, and follow from the more general rules.
*)

Definition colim_N (F : nat -> Type) (f : forall n : nat, F n -> F(S n)) : Type :=
  colimit (Build_sequence F f).

Definition inc (F : nat -> Type) (f : forall n : nat, F n -> F(S n)) (n : nat) (x : F n) : colim_N F f
  := @colim mappingtelescope_graph (Build_sequence F f) n x.

Definition com (F : nat -> Type) (f : forall n : nat, F n -> F(S n)) (n : nat) (x : F n) :
  inc F f (S n) (f n x) = inc F f n x.
Proof.
compute.
pose (@colimp mappingtelescope_graph (Build_sequence F f) n (S n) (reflexivity (S n)) x).
compute in p.
eapply p.
Defined.

Definition cocone_P 
  (P : Type)
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (Pi : forall (n : nat), F n -> P)
  (Pc : forall (n : nat) (x : F n), Pi (S n) (f n x) = Pi n x)
  : cocone (Build_sequence F f) P.
Proof.
simple refine (Build_cocone _ _).
- eapply Pi.

- cbn.
  intros.
  induction g.
  eapply Pc.
Defined.

Definition colim_N_rec
  (P : Type)
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (Pi : forall (n : nat), F n -> P)
  (Pc : forall (n : nat) (x : F n), Pi (S n) (f n x) = Pi n x) :
  colim_N F f -> P
  := @colimit_rec mappingtelescope_graph (Build_sequence F f) P (cocone_P P F f Pi Pc).

Definition colim_N_rec_beta_com
  (P : Type)
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (Pi : forall (n : nat), F n -> P)
  (Pc : forall (n : nat) (x : F n), Pi (S n) (f n x) = Pi n x)
  (n : nat)
  (x : F n) :
  ap (colim_N_rec P F f Pi Pc) (com F f n x) = Pc n x.
Proof.
assert
 (ap
    (@colimit_rec mappingtelescope_graph (Build_sequence F f) P
       (cocone_P P F f Pi Pc))
    (@colimp mappingtelescope_graph (Build_sequence F f) n n.+1
       (reflexivity n.+1) x) =
  qq (cocone_P P F f Pi Pc) n n.+1 (reflexivity n.+1) x).
- apply (colimit_rec_beta_colimp P (cocone_P P F f Pi Pc) n 
     (S n) (reflexivity (S n)) x).

- cbn in X.
  apply X.
Defined.

Definition colim_N_ind
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (P : colim_N F f -> Type)
  (Pi : forall (n : nat), forall (x : F n), P (inc F f n x))
  (Pc : forall (n : nat) (x : F n), (com F f n x) # Pi (S n) (f n x) = Pi n x) :
  forall (x : colim_N F f), P x.
Proof.
simple refine (colimit_ind _ _ _) ; cbn.
- apply Pi.
- intros.
  induction g.
  apply Pc.
Defined.

(*
The colimit of F(X) = A is A.
Lemma 10 in paper.
*)
Section ColimConst.

Variable A : Type.
Definition c_fam := fun (_ : nat) => A.
Definition c_map := fun (_ : nat) => fun (x : A) => x.

(*
colim A id -> A
Defined by F(n) -> A as id.
*)
Definition CC_A :
  colim_N c_fam c_map -> A.
Proof.
Proof.
simple refine (colim_N_rec _ _ _ _ _).
- intro n.
  apply idmap.
- cbn.
  intros.
  reflexivity.
Defined.

Definition A_CC (a : A) : colim_N c_fam c_map :=
  inc c_fam c_map 0 a.

Definition iso_CC_A (x : A) :
  CC_A (A_CC x) = x := reflexivity x.

Definition iso_A_CC :
  forall (x : colim_N c_fam c_map), A_CC (CC_A x) = x.
Proof.
simple refine (colim_N_ind _ _ _ _ _).
- cbn.
  intros n x.
  induction n.
  * reflexivity.
  * apply (IHn x @ (com c_fam c_map n x)^).
- cbn.
  intros.
  rewrite @HoTT.Types.Paths.transport_paths_FlFr.
  rewrite ap_compose.
  rewrite ap_idmap.
  hott_simpl.
  rewrite ap_V.
  unfold CC_A.
  rewrite (colim_N_rec_beta_com A c_fam c_map).
  hott_simpl.
Defined.

Theorem BiInv_CC_A : BiInv CC_A.
Proof.
split.
- exists A_CC.
  unfold Sect.
  apply iso_A_CC.
- exists A_CC.
  unfold Sect.
  apply iso_CC_A.
Qed.

Theorem Equiv_CC_A : IsEquiv CC_A.
Proof.
apply isequiv_biinv.
apply BiInv_CC_A.
Qed.

End ColimConst.


(*
Colimits as coequalizers of sums
*)
Module Export ColimAsCoeq.

Parameter G : graph.
Parameter D : diagram G.

Definition C1 := sigT (diagram0 D).
Definition B := sigT (fun i : G => D i * sigT (fun j : G => G i j)).

Definition g1 (x : B) : C1.
Proof.
destruct x as (i, y).
destruct y as (x, _).
exists i.
apply x.
Defined.

Definition g2 (x : B) : C1.
Proof.
destruct x as (i, y).
destruct y as (x, z).
destruct z as (j, g).
exists j.
apply (diagram1 D g x).
Defined.

Definition C : Type0 := Coeq g1 g2.
Definition H : Type0 := colimit D.

Definition CToH : C -> H.
Proof.
simple refine (Coeq_rec _ _ _).
- unfold C1.
  intro y.
  destruct y as (x, z).
  unfold H.
  apply (colim x z).
- intros.
  destruct b as (i, x).
  destruct x as (x, y).
  destruct y as (j, g).
  simpl.
  apply (colimp i j g x)^.
Defined.

Definition HToC : H -> C.
Proof.
simple refine (colimit_rec _ _).
simple refine (Build_cocone _ _).
- intros i x.
  apply coeq.
  exists i.
  apply x.
- intros.
  simpl.
  pose (@cp B C1 g1 g2).
  unfold B in p.
  apply (p (existT _ i (x, existT _ j g)))^.
Defined.

Theorem CToHEq :
  forall (x : C), HToC(CToH x) = x.
Proof.
simple refine (Coeq_ind _ _ _).
- intros.
  destruct a as [i x].
  reflexivity.
- intros.
  destruct b as [i z].
  destruct z as [x z].
  destruct z as [j g].
  rewrite @HoTT.Types.Paths.transport_paths_FlFr.
  rewrite ap_idmap.
  rewrite ap_compose.
  rewrite concat_p1.
  rewrite Coeq_rec_beta_cp.
  rewrite ap_V.
  rewrite inv_V.
  rewrite colimit_rec_beta_colimp.
  hott_simpl.
Defined.

Theorem HToCEq :
  forall (x : H), CToH(HToC x) = x.
Proof.
simple refine (colimit_ind _ _ _).
- intros.
  reflexivity.
- intros.
  rewrite @HoTT.Types.Paths.transport_paths_FlFr.
  rewrite ap_idmap.
  rewrite ap_compose.
  rewrite concat_p1.
  rewrite colimit_rec_beta_colimp.
  cbn.
  rewrite ap_V.
  rewrite Coeq_rec_beta_cp.
  hott_simpl.
Defined.

End ColimAsCoeq.