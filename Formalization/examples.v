Require Import HoTT.
Require Import hit_structure.

(* To test whether out definition makes sense, we show that various HITs from the HoTT
   library are HITs according to our definition. *)

(* Example: nat is a hit. *)
Definition nat_hit : HIT nat_signature.
Proof.
  simple refine {| hit_carrier := nat |}.

  - intros [ | ].
    + intros _ ; exact 0.
    + exact S.

  - intro i ; elim i.

  - intros F c p x.
    induction x as [| n y].
    + exact (c true tt tt).
    + apply (c false n y).

  - intros F c p [ | ] [] ; reflexivity.

  - intros _ [].
Defined.

(* Example: the HoTT library circle is a HIT *)
Definition circle_hit : HIT circle_signature.
Proof.
  simple refine {| hit_carrier := S1 ;
                   hit_point := (fun _ _ => base) ;
                   hit_path := (fun _ _ => _ ) |}.
  - exact loop.

  - intros F c f x.
    now apply (S1_ind F (c tt tt tt)), (f tt).

  - intros F c p [] [] ; reflexivity.

  - intros F [] c p [] [].
    apply S1_ind_beta_loop.
Defined.

(* Example: the HoTT library suspension is a HIT *)

Definition suspension_hit (A : Type) : HIT (suspension_signature A).
Proof.
  simple refine {| hit_carrier := Susp A |}.

  - intros [_|_] ; [exact South | exact North].

  - intros [] x ; exact (merid x).

  - intros F c f x.
    apply (Susp_ind F (c false tt tt) (c true tt tt)).
    intro a.
    apply (f tt _ a).

  - intros F c p [|] [] ; reflexivity.

  - intros F [] c p [] a.
    simpl in *.
    apply Susp_ind_beta_merid with (x := a).
Defined.

