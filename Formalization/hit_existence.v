(* We formulate the main theorem, which states that all HITs exist, provided that several
   kinds of HITs do. *)

Require Import HoTT.
Require Import hit_structure.
Require Import colim.

Theorem HIT_existence (Σ : hit_signature) : HIT Σ.
Proof.
  (* here we should construct the hit in question using
     only the "three" hits. These we will take from the
     HoTT library, so that we get judgmental computation
     rules for points. The alternative would be to assume
     that the theorem holds for certain specific instances
     of [Σ] and prove that all the others follow. But that
     would likely be quite a bit more technically involved.
  *)
  admit.
Admitted.
