Require Import HoTT.

Require Import polynomial.

Axiom cheating : forall A : Type, A.
Ltac todo := apply cheating.
Axiom magic : forall A B, A -> B.

Section Endpoints.
(* The definition of a HIT signature and a HIT for the signature. *)

(* An endpoint is also called a "constructor term". It is used in
   the HIT signature to describe the endpoints of path constructors. *)

(*
   Endpoints are parameterized by a family of polynomials which will
   be specialized to the point constructors in the definition of HITS.
*)
Variable I : Type.
Variable C : I -> polynomial.

Inductive endpoint :
  polynomial -> polynomial -> Type :=
  | endpoint_var : forall {P}, endpoint P P
  | endpoint_const : forall {P} {T : Type}, T -> endpoint P (poly_const T)
  | endpoint_constr : forall {P} (i : I), endpoint P (C i) -> endpoint P poly_var
  | endpoint_fst : forall {P Q R}, endpoint P (poly_times Q R) -> endpoint P Q
  | endpoint_snd : forall {P Q R}, endpoint P (poly_times Q R) -> endpoint P R
  | endpoint_pair : forall {P Q R}, endpoint P Q -> endpoint P R -> endpoint P (poly_times Q R)
  | endpoint_inl : forall {P Q R}, endpoint P Q -> endpoint P (poly_plus Q R)
  | endpoint_inr : forall {P Q R}, endpoint P R -> endpoint P (poly_plus Q R)
.

Variable A : Type.
Variable F : A -> Type.
Variable c : forall i, poly_act (C i) A -> A.
Variable f : forall (i : I) (u : poly_act (C i) A), poly_fam (C i) F u -> F (c i u).

(* Endpoint acting on data for point constructors. *)
Fixpoint endpoint_act
  {P Q : polynomial}
  (e : endpoint P Q) (* the endpoint *)
  {struct e}
  : poly_act P A -> poly_act Q A.
Proof.
  destruct e.

  (* endpoint_var *)
  - exact (fun u => u).

  (* endpoint_const *)
  - exact (fun _ => t).

  (* endpoint_constr *)
  - exact (fun u => c i (endpoint_act _ _ e u)).

  (* endpoint_fst *)
  - exact (fun u => fst (endpoint_act _ _ e u)).

  (* endpoint_snd *)
  -  exact (fun u => snd (endpoint_act _ _ e u)).

  (* endpoint_pair *)
  - exact  (fun u => (endpoint_act _ _ e1 u, endpoint_act _ _ e2 u)).

  (* endpoint_inl *)
  -  exact (fun u => inl (endpoint_act _ _ e u)).

  (* endpoint_inr *)
  -  exact (fun u => inr (endpoint_act _ _ e u)).
Defined.

(* The dependent action of an endpoint, this is used for
   "lifting" the path constructors in the elimnation principle. *)
Fixpoint endpoint_dact
         {P Q : polynomial}
         (e : @endpoint P Q)
         {struct e} :
  forall (x : poly_act P A) (h : poly_fam P F x), poly_fam Q F (endpoint_act e x).
Proof.
  simple refine (
           match e as z in endpoint P Q
                 return (forall (x : poly_act P A) (h : poly_fam P F x), poly_fam Q F (endpoint_act z x))
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
  - exact (fun _ x => x).

  (* endpoint_const *)
  - exact (fun _ _ => t).

  (* endpoint_constr *)
  - { intros x h.
      apply f.
      apply endpoint_dact.
      - exact h.
    }

  (* endpoint_fst *)
  - { intros x h.
      apply (@fst _ (poly_fam p1 F (endpoint_act (endpoint_snd u) x))).
      apply @endpoint_dact with (Q := poly_times p0 p1).
      + exact h.
    }

  (* endpoint_snd *)
  - { intros x h.
      apply (@snd (poly_fam p0 F (endpoint_act (endpoint_fst u) x))).
      apply @endpoint_dact with (Q := poly_times p0 p1).
      + exact h.
    }

  (* endpoint_pair *)
  - { intros x h.
      split.
      - apply endpoint_dact.
        + exact h.
      - apply endpoint_dact.
        + exact h.
    }

  (* endpoint_inl *)
  - { intros x h.
      apply endpoint_dact with (e := e).
      + exact h.
    }

  (* endpoint_inr *)
  - { intros x h.
      apply endpoint_dact with (e := e).
      + exact h.
    }
Defined.

(* If [h] commutes with constructors, then it commutes with all endpoints. *)
Fixpoint endpoint_dact_compute
  (P Q : polynomial)
  (x : poly_act P A)
  (e : endpoint P Q)
  (h : forall x, F x)
  {struct e}
:
  (forall i u, h (c i u) = f i u (poly_dmap (C i) h u)) ->
  endpoint_dact e x (poly_dmap P h x) = poly_dmap Q h (endpoint_act e x).
Proof.
  intro H.
  destruct e.

  (* endpoint_var *)
  - { reflexivity. }

  (* endpoint_const *)
  - { reflexivity. }

  (* endpoint_constr *)
  - { simpl.
      transitivity (f i (endpoint_act e x) (poly_dmap (C i) h (endpoint_act e x))).
      - apply ap, endpoint_dact_compute, H.
      - symmetry ; apply H.
    }

  (* endpoint_fst *)
  - { simpl.
      rewrite (endpoint_dact_compute _ _ _ e).
      reflexivity.
      apply H.
    }

  (* endpoint_snd *)
  - { simpl.
      rewrite (endpoint_dact_compute _ _ _ e).
      reflexivity.
      apply H.
    }

  (* endpoint_pair *)
  - { apply path_prod ; apply endpoint_dact_compute, H. }

  (* endpoint_inl *)
  - { apply endpoint_dact_compute with (e := e), H. }

  (* endpoint_inr *)
  - { apply endpoint_dact_compute with (e := e), H. }
Defined.

(* A general HIT might have an arbitrary number of endpoints and therefore an arbitrarily
   nested point constructors. Our construction of a HIT presumes that there is a bound to
   the nesting. We define here what it means for an endpoint to have such a bound. *)
Inductive endpoint_rank : forall {P Q}, endpoint P Q -> nat -> Type :=
  | rank_var : forall {P} (n : nat), endpoint_rank (@endpoint_var P) n
  | rank_const : forall {P} {T : Type} (t : T) (n : nat), endpoint_rank (@endpoint_const P _ t) n
  | rank_constr : forall {P} (i : I) (n : nat) (e : endpoint P (C i)),
      endpoint_rank e n -> endpoint_rank (endpoint_constr i e) (S n)
  | rank_fst : forall {P Q R} (n : nat) (e : endpoint P (poly_times Q R)),
      endpoint_rank e n -> endpoint_rank (endpoint_fst e) n
  | rank_snd : forall {P Q R} (n : nat) (e : endpoint P (poly_times Q R)),
      endpoint_rank e n -> endpoint_rank (endpoint_snd e) n
  | rank_inl : forall {P Q R} (n : nat) (e : endpoint P Q),
      endpoint_rank e n -> endpoint_rank (@endpoint_inl _ _ R e) n
  | rank_inr : forall {P Q R} (n : nat) (e : endpoint P R),
      endpoint_rank e n -> endpoint_rank (@endpoint_inr _ Q _ e) n.

End Endpoints.

Arguments endpoint {_} _ _ _.
Arguments endpoint_var {_ _} {_}.
Arguments endpoint_const {_ _} {_} {_} _.
Arguments endpoint_constr {_ _} {_} _ _ .
Arguments endpoint_fst {_ _} {_ _ _} _.
Arguments endpoint_snd {_ _} {_ _ _} _.
Arguments endpoint_pair {_ _} {_ _ _} _ _.
Arguments endpoint_inl {_ _} {_ _ _} _.
Arguments endpoint_inr {_ _} {_ _ _} _.

Arguments endpoint_act {_ _ _} _ {P Q} _ _.
Arguments endpoint_dact {I C A F} c _ {P Q} _ _ _.
Arguments endpoint_dact_compute {_ _ _} _ _ _ {P Q} _ _ _ _.

Arguments endpoint_rank {_} _ {_ _} _ _.

(* A HIT signature is specified by point constructors and path constructors.

   Note: we are allowing an arbitrary family of poitn and path construcrors.
         We will restrict them later on in existence theorem.
*)
Structure hit_signature := {
  (* indexing for point constructors *)
  sig_point_index : Type ;

  (* the signatures for point constructors *)
  sig_point : sig_point_index -> polynomial ;

  (* indexing for path constructors *)
  sig_path_index : Type ;

  (* the parameters of each path constructor *)
  sig_path_param : sig_path_index -> polynomial ;

  (* the left and right endpoints of path constructors *)
  sig_path_lhs : forall i, endpoint sig_point (sig_path_param i) poly_var ;
  sig_path_rhs : forall i, endpoint sig_point (sig_path_param i) poly_var
}.

(* A HIT signature has rank [n] if all of its endpoints do. *)
Definition hit_rank Σ n :=
  (forall j, endpoint_rank (sig_point Σ) (sig_path_lhs Σ j) n) *
  (forall j, endpoint_rank (sig_point Σ) (sig_path_rhs Σ j) n).

(* Example: propositional truncation *)
Definition trunc_signature (A : Type) :=
  {|
    sig_point_index := Unit ;
    sig_point := (fun _ => poly_const A) ;
    sig_path_index := Unit ;
    sig_path_param := (fun _ => poly_times poly_var poly_var) ;
    sig_path_lhs := (fun _ => endpoint_fst endpoint_var) ;
    sig_path_rhs := (fun _ => endpoint_snd endpoint_var)
  |}.

(* Example: circle *)

Definition circle_signature :=
  {|
    sig_point_index := Unit ;
    sig_point := (fun _ => poly_const Unit) ;
    sig_path_index := Unit ;
    sig_path_param := (fun _ => poly_const Unit) ;
    sig_path_lhs := (fun _ => endpoint_constr tt endpoint_var) ;
    sig_path_rhs := (fun _ => endpoint_constr tt endpoint_var)
  |}.

(* Example: susupension *)

Definition suspension_signature (A : Type) :=
  {|
    sig_point_index := Bool ;
    sig_point := (fun _ => poly_const Unit) ;
    sig_path_index := Unit ;
    sig_path_param := (fun _ => poly_const A) ;
    sig_path_lhs := (fun _ => endpoint_constr false (endpoint_const tt)) ;
    sig_path_rhs := (fun _ => endpoint_constr true (endpoint_const tt))
  |}.

(* Example: natural numbers *)
Definition nat_signature :=
  {|
    sig_point_index := Bool ;
    sig_point := (fun b => if b then poly_const Unit else poly_var) ;
    sig_path_index := Empty ;
    sig_path_param := Empty_rect _ ;
    sig_path_lhs := Empty_rect _ ;
    sig_path_rhs := Empty_rect _
  |}.


Section HIT_Definition.

(* We define HIT for signature [Σ]. *)
Variable Σ : hit_signature.

(* The type of a lift of the point constructor [c] over a family [F]. *)
Definition point_over
  {H : Type} (* the carrier type *)
  (F : H -> Type)
  (c : forall i, poly_act (sig_point Σ i) H -> H) (* point constructors *)
  (p : forall j u, endpoint_act c (sig_path_lhs Σ j) u =
              endpoint_act c (sig_path_rhs Σ j) u) (* path constructors *)
  :=
  forall i (u : poly_act (sig_point Σ i) H), poly_fam (sig_point Σ i) F u -> F (c i u).


(* The type of a lift of the path constructor [p] over a family [F]. *)
Definition path_over
  {H : Type}
  {F : H -> Type}
  {c : forall i, poly_act (sig_point Σ i) H -> H} (* point constructors *)
  {p : forall j u, endpoint_act c (sig_path_lhs Σ j) u =
              endpoint_act c (sig_path_rhs Σ j) u} (* path constructors *)
  (c' : point_over F c p)
  :=
  forall j
    (x : poly_act (sig_path_param Σ j) H)
    (h : poly_fam (sig_path_param Σ j) F x),
    transport _ (p j x) (endpoint_dact c c' (sig_path_lhs Σ j) x h) =
    endpoint_dact c c' (sig_path_rhs Σ j) x h.


(* It is tricky to phrase the computation rule for paths, so we phrase an auxiliary lemma
   that lets us construct the type of the path computation rule interactively. *)
Definition hit_path_beta_eq
  (H : Type) (* the carrier type *)
  (c : forall i, poly_act (sig_point Σ i) H -> H) (* point constructors *)
  (p : forall j u, endpoint_act c (sig_path_lhs Σ j) u =
              endpoint_act c (sig_path_rhs Σ j) u) (* path constructors *)
  (E : (* the eliminator *)
       forall (F : H -> Type)
         (c' : point_over F c p)
         (p' : path_over c'),
         forall (x : H), F x)
  (point_beta : (* the point computation rule *)
    forall (F : H -> Type)
      (c' : point_over F c p)
      (p' : path_over c')
      i (t : poly_act (sig_point Σ i) H),
      E F c' p' (c i t) = c' i t (poly_dmap (sig_point Σ i) (E F c' p') t)) :
  Type.
Proof.
  simple refine (forall (F : H -> Type) (j : sig_path_index Σ)
                   (c' : point_over F c p)
                   (p' : path_over c')
                   (k : sig_path_index Σ)
                   (t : poly_act (sig_path_param Σ k) H), _).
  (* We want an equation between [α] and [β], but their types do not match, so a transport
     is required on each side of the equation. *)
  pose (α := apD (E F c' p') (p k t)).
  pose (β := p' k t (poly_dmap _ (E F c' p') t)).
  simpl in β.
  (* the path along which we will transport lhs *)
  assert (q_lhs : endpoint_dact c c' (sig_path_lhs Σ k) t (poly_dmap (sig_path_param Σ k) (E F c' p') t) =
              E F c' p' (endpoint_act c (sig_path_lhs Σ k) t)).
  { apply (endpoint_dact_compute F c c' t (sig_path_lhs Σ k)), point_beta. }
  (* the path along which we will transport rhs *)
  assert (q_rhs : endpoint_dact c c' (sig_path_rhs Σ k) t (poly_dmap (sig_path_param Σ k) (E F c' p') t) =
              E F c' p' (endpoint_act c (sig_path_rhs Σ k) t)).
  { apply (endpoint_dact_compute F c c' t (sig_path_rhs Σ k)), point_beta. }
  pose (β' := transport
              (fun z => transport F (p k t) z =
                     endpoint_dact c c' (sig_path_rhs Σ k) t (poly_dmap (sig_path_param Σ k) (E F c' p') t))

              q_lhs β).
  simpl in β'.
  pose (β'' := transport
                (fun z => transport F (p k t) (E F c' p' (endpoint_act c (sig_path_lhs Σ k) t)) = z)
                q_rhs β').
  exact (α = β'').
Defined.

Structure HIT :=
{
  (* the carrier of the HIT *)
  hit_carrier :> Type ;

  (* the point constructor *)
  hit_point : forall i, poly_act (sig_point Σ i) hit_carrier -> hit_carrier ;

  (* path constructors *)
  hit_path : forall j u, endpoint_act hit_point (sig_path_lhs Σ j) u =
                    endpoint_act hit_point (sig_path_rhs Σ j) u ;

  (* the eliminator *)
  hit_ind :
    forall (F : hit_carrier -> Type)
      (c : point_over F hit_point hit_path)
      (p : path_over c)
      (x : hit_carrier),
      F x ;

  (* computation rule for points *)
  hit_point_beta :
    forall (F : hit_carrier -> Type)
      (c : point_over F hit_point hit_path)
      (p : path_over c)
      (i : sig_point_index Σ)
      (t : poly_act (sig_point Σ i) hit_carrier),
        hit_ind F c p (hit_point i t) =
        c i t (poly_dmap (sig_point Σ i) (hit_ind F c p) t) ;

  (* computation rule for paths *)
  hit_path_beta :
    hit_path_beta_eq hit_carrier hit_point hit_path hit_ind hit_point_beta
}.
End HIT_Definition.

Arguments hit_point {_ _} _ _.
Arguments hit_path {_ _} _ _.
Arguments hit_ind {_ _} _ _ _ _.
