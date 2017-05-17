(* We formulate the main theorem, which states that all HITs exist, provided that several
   kinds of HITs do. *)

Require Import HoTT.
Require Import HoTT.Pointed.
Require Import polynomial.
Require Import hit_structure.

(* An auxiliary definition of finite set. *)
Definition fin (n : nat) := {i : nat & i <= n}.

(* Suppose we have a finite sequence

   [X 0 -> X 1 -> ... -> X m]

   with transitions [ι_k : X k -> X (k + 1)], approximating the hit for [Σ].
   We call such a sequence a *finite telescope*.

   We may then extend the sequence by one more level of approximation

   [X m -> X (m+1)]

   by constructing [X (m+1)] as the HIT:

   - point constructors:
     * inclusion [ι_m : X m -> X (m+1)]
     * point constructors from [Σ], taking arguments in
       [X m] and giving values in [X (m+1)]

   - path constructors:
     * paths from [Σ], with endpoints of paths interpreted suitably in the previous stages [X i].
     * 2D-paths expressing the fact that the path constructors commute with the inclusions [ι_m].

  We formalize this idea here.
*)

Section TelescopeStage.
(* Construction of [X (m+1)] from the diagram [X 0 -> ... -> X m], see above. *)

Variable Σ : hit_signature.

(* The type of a finite telescope. We will actually always start a telescope with the [Empty] type. *)
Record FiniteTelescope : Type := {
  tele_tip : Type ;
  tele_rec : option { t : FiniteTelescope & tele_tip t -> tele_tip }
}.

Inductive FiniteTelescope : Type := {
}.
  | ocular : Type -> FiniteTelescope
  | tip : 

with Stage : Type :=
  | 

  tele_length : nat ;
  tele_type :> fin tele_length -> Type ;
  tele_incl : forall i, tele_type i -> tele_type (S i)
}.
  match n with
  | 0 => Empty
  | S n => { T : FiniteTelescope n & { X : Type 
  end.


Variable X : nat -> Type.
Variable ι : forall n, Y (S n) -> Y n.

(* Let us explain the next construction via an example. Suppose we have a binary
   point constructor [c] and a path constructor expressing associativity:

   [ assoc x y z : c (c (x, y), z) = c (x, c (y, z)) ]

   The new stage [Z 0] is constructed as a HIT as follows. There are two kinds of points:

     * inclusion of previous stage: for every [a : Y 0] there is [ ι a : Z 0]

     * new points: for all [a b : Y 0] there is a point [c (a, b) : Z 0].

   The path constructors are:

     * various coherence equations expressing commutativity of inclusions [ι] and [c]

     * associativity equations (read this carefully): for all [a : Y 0





Fixpoint endpoint_stage_act {P Q} (e : endpoint (sig_point Σ) P Q) :
  forall k, poly_act Q (X k).
Proof.
  simple refine (
           match e in endpoint _ P Q return poly_act Q (X k) with
           | endpoint_var _ => _
           | endpoint_const _ _ t => _
           | endpoint_constr _ i u => _
           | endpoint_fst _ _ _ u => _
           | endpoint_snd _ _ _ u => _
           | endpoint_pair _ _ _ u v => _
           | endpoint_inl _ _ _ e => _
           | endpoint_inr _ _ _ e => _
           end).

  (* endpoint_var *)
  - { apply (endpoint_stage_act (sig_point Σ)).

  (* endpoint_const *)
  - { exact (stage_ty Σ X ι). }

  (* endpoint_constr *)
  - {  
    }

  (* endpoint_fst *)
  - { admit. }

  (* endpoint_snd *)
  - { admit. }

  (* endpoint_pair *)
  - { admit. }

  (* endpoint_inl *)
  - { admit. }

  (* endpoint_inr *)
  - { admit. }



(* The underlying type of the next level. *)
Inductive stage_ty : Type :=
  (* the inclusion into the next stage *)
  | stage_incl : X 0 -> stage_ty
  (* one extra level of point constructors *)
  | stage_constr : forall i, poly_act (sig_point Σ i) (X 0) -> stage_ty.

(* The path constructors are quite a bit trickier.
   We being by defining how to interpret their endpoints. *)

Fixpoint endpoint_stage_ty
         (Σ : hit_signature)
         (X : nat -> Type)
         (ι : forall n, X n -> X (S n))
         (k : nat)
         {P Q} (e : endpoint (sig_point Σ) P Q)
         {struct e}
  : X k.
Proof.
  simple refine (
           match e return X k with
           | endpoint_var _ => _
           | endpoint_const _ _ t => _
           | endpoint_constr _ i u => _
           | endpoint_fst _ _ _ u => _
           | endpoint_snd _ _ _ u => _
           | endpoint_pair _ _ _ u v => _
           | endpoint_inl _ _ _ e => _
           | endpoint_inr _ _ _ e => _
           end).

  (* endpoint_var *)
  - { exact (stage_ty Σ X ι). }

  (* endpoint_const *)
  - { exact (stage_ty Σ X ι). }

  (* endpoint_constr *)
  - {  
    }

  (* endpoint_fst *)
  - { admit. }

  (* endpoint_snd *)
  - { admit. }

  (* endpoint_pair *)
  - { admit. }

  (* endpoint_inl *)
  - { admit. }

  (* endpoint_inr *)
  - { admit. }





(* The action of an endpoint on a telescope [X]. *)
Fixpoint stage_endpoint
         (Σ : hit_signature)
         (X : nat -> Type)
         (ι : forall n, X n -> X (S n))
         {P Q} (e : endpoint (sig_point Σ) P Q) (n : nat)
  : poly_act P (stage_point Σ X ι) -> poly_act Q (stage_point Σ X ι).
Proof.
  simple refine (
           match e as z in endpoint _ P Q
                 return poly_act P (stage_point Σ X ι) -> poly_act Q (stage_point Σ X ι)
           with
           | endpoint_var _ => _
           | endpoint_const _ _ t => _
           | endpoint_constr _ i u => _
           | endpoint_fst _ _ _ u => _
           | endpoint_snd _ _ _ u => _
           | endpoint_pair _ _ _ u v => _
           | endpoint_inl _ _ _ e => _
           | endpoint_inr _ _ _ e => _
           end).

  (* endpoint_var *)
  - { exact (fun x => x). }

  (* endpoint_const *)
  - { exact (fun _ => t). }

  (* endpoint_constr *)
  - {  
    }

  (* endpoint_fst *)
  - { admit. }

  (* endpoint_snd *)
  - { admit. }

  (* endpoint_pair *)
  - { admit. }

  (* endpoint_inl *)
  - { admit. }

  (* endpoint_inr *)
  - { admit. }







(* TODO: define the rest of the structure. *)

End TelescopeStage.

Section HitTelescope.

Variable (Σ : hit_signature).

(* The existing sequence and transitions between them. *)
Variable (X : nat -> Type).
Variable (ι : forall n, X (S n) -> X n).

Definition extend_telescope : { Y : Type & κ : X 0 -> Y }.


End HitTelescope.

(* A HIT exists for any signtature with a rank. *)
Theorem HIT_existence (Σ : hit_signature) :
  { n : nat & hit_rank Σ n } -> HIT Σ.
  (* NOTE: it ought to be the case that we could assume a *mere* existence of [n] here,
           because if [n] merely exists, then it exists. For that to be the case, we need
           two lemmas:

           1. If [rank Σ n] and [n <= m] then [rank Σ m].
           2. rank is decidable in [n], i.e., [forall n, rank Σ n + ~ (rank Σ n)]
   *)
Proof.
  intros [n has_rank].
  (* here we should construct the hit in question using only the "three" hits. These we
     will take from the HoTT library, so that we get judgmental computation rules for
     points. The alternative would be to assume that the theorem holds for certain
     specific instances of [Σ] and prove that all the others follow. But that would likely
     be quite a bit more technically involved. *)
  admit.
Admitted.
