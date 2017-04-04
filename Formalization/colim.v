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

Definition colim_N (F : nat -> Type) (f : forall n : nat, F n -> F(S n)) : Type :=
  colimit (Build_sequence F f).

Definition inc (F : nat -> Type) (f : forall n : nat, F n -> F(S n)) (n : nat) (x : F n) : colim_N F f
  := @colim mappingtelescope_graph (Build_sequence F f) n x.

Definition com {F : nat -> Type} {f : forall n : nat, F n -> F(S n)} (n : nat) (x : F n) :
  inc F f n x = inc F f (S n) (f n x).
Proof.
compute.
symmetry.
pose (@colimp mappingtelescope_graph (Build_sequence F f) n (S n) (reflexivity (S n)) x).
compute in p.
apply p.
Defined.

(*
The colimit of F(X) = A is A.
Lemma 10 in paper.
*)
Section ColimConst.

(*
colim A id -> A
Defined by F(n) -> A as id.
*)
Definition CC_A (A : Type) :
  colim_N (fun (_ : nat) => A) (fun (_ : nat) => idmap) -> A.
Proof.
refine (colimit_rec _ _).
simple refine (Build_cocone _ _).
- cbn.
  intros.
  apply X.

- cbn.
  intros.
  induction g.
  reflexivity.
Defined.

Definition A_CC (A : Type) (a : A) : colim_N (fun (_ : nat) => A) (fun (_ : nat) => idmap) :=
  inc (fun (_ : nat) => A) (fun (_ : nat) => idmap) 0 a.

Definition iso_CC_A (A : Type) (x : A) :
  CC_A A (A_CC A x) = x := reflexivity x.

Definition iso_A_CC (A : Type) :
  forall (x : colim_N (fun (_ : nat) => A) (fun (_ : nat) => idmap)), A_CC A (CC_A A x) = x.
Proof.
simple refine (colimit_ind _ _ _).
- cbn.
  intros n x.
  induction n.
  * reflexivity.
  * rewrite IHn.
    pose (com n x: inc (fun (_ : nat) => A) (fun (_ : nat) => idmap) n x  = inc (fun (_ : nat) => A) (fun (_ : nat) => idmap) (S n) x).
    compute in p.
    apply p.
admit.
Admitted.