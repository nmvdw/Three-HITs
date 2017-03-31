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
Variable I: Type.
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

(* Endpoint acting on data for point constructors. *)
Fixpoint endpoint_act
  {P Q : polynomial}
  {A : Type} (* carrier *)
  (c : forall i, poly_act (C i) A -> A) (* point constructors *)
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
  - exact (fun u => c i (endpoint_act _ _ _ c e u)).

  (* endpoint_fst *)
  - exact (fun u => fst (endpoint_act _ _ _ c e u)).

  (* endpoint_snd *)
  -  exact (fun u => snd (endpoint_act _ _ _ c e u)).

  (* endpoint_pair *)
  - exact  (fun u => (endpoint_act _ _ _ c e1 u, endpoint_act _ _ _ c e2 u)).

  (* endpoint_inl *)
  -  exact (fun u => inl (endpoint_act _ _ _ c e u)).

  (* endpoint_inr *)
  -  exact (fun u => inr (endpoint_act _ _ _ c e u)).
Defined.

(* The dependent action of an endpoint, this is used for
   "lifting" the path constructors in the elimnation principle. *)
Fixpoint endpoint_dact
         {Q R : polynomial}
         {A : Type}
         (c : forall i, poly_act (C i) A -> A)
         (F : A -> Type)
         (f : forall (i : I) (u : poly_act (C i) A), poly_fam (C i) F u -> F (c i u))
         (e : @endpoint Q R)
         {struct e} :
  forall (x : poly_act Q A) (h : poly_fam Q F x), poly_fam R F (endpoint_act c e x).
Proof.
  simple refine (
           match e as z in @endpoint Q R
                 return (forall (x : poly_act Q A) (h : poly_fam Q F x), poly_fam R F (endpoint_act c z x))
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
      - exact f.
      - exact h.
    }

  (* endpoint_fst *)
  - { intros x h.
      apply (@fst _ (poly_fam p1 F (endpoint_act c (endpoint_snd u) x))).
      apply @endpoint_dact with (R := poly_times p0 p1).
      + exact f.
      + exact h.
    }

  (* endpoint_snd *)
  - { intros x h.
      apply (@snd (poly_fam p0 F (endpoint_act c (endpoint_fst u) x))).
      apply @endpoint_dact with (R := poly_times p0 p1).
      + exact f.
      + exact h.
    }

  (* endpoint_pair *)
  - { intros x h.
      split.
      - apply endpoint_dact.
        + exact f.
        + exact h.
      - apply endpoint_dact.
        + exact f.
        + exact h.
    }

  (* endpoint_inl *)
  - { intros x h.
      apply endpoint_dact with (e := e).
      + exact f.
      + exact h.
    }

  (* endpoint_inr *)
  - { intros x h.
      apply endpoint_dact with (e := e).
      + exact f.
      + exact h.
    }
Defined.

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

Arguments endpoint_act {_ _} {_ _ _} _ _ _.
Arguments endpoint_dact {_ _} {_ _ _} _ _ _ _ _ _.

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

(* Given a carrier type [A], we want to explain what the structure
   of a HIT on [A] is. For this purpose we need to define the types
   of the point constructors, the paths, and intro rules, and the
   eliminator. *)

(* We now define what a HIT is. *)

Structure HIT (Σ : hit_signature) :=
{
  (* the carrier of the HIT *)
  hit_carrier :> Type ;

  (* the point constructor *)
  hit_point : forall i, poly_act (sig_point Σ i) hit_carrier -> hit_carrier ;

  (* path constructors *)
  hit_path : forall i u, endpoint_act hit_point (sig_path_lhs Σ i) u =
                    endpoint_act hit_point (sig_path_rhs Σ i) u ;

  (* the eliminator *)
  hit_ind :
    forall (F : hit_carrier -> Type)
      (c : forall i (u : poly_act (sig_point Σ i) hit_carrier),
          poly_fam (sig_point Σ i) F u -> F (hit_point i u))
      (p : forall i
             (x : poly_act (sig_path_param Σ i) hit_carrier)
             (h : poly_fam (sig_path_param Σ i) F x),
               transport _ (hit_path i x)
               (endpoint_dact hit_point F c (sig_path_lhs Σ i) x h) =
               endpoint_dact hit_point F c (sig_path_rhs Σ i) x h)
      (x : hit_carrier),
      F x ;

  (* computation rule for points *)
  hit_point_beta :
    forall (F : hit_carrier -> Type)
      (c : forall i (u : poly_act (sig_point Σ i) hit_carrier),
          poly_fam (sig_point Σ i) F u -> F (hit_point i u))
      (p : forall i
             (x : poly_act (sig_path_param Σ i) hit_carrier)
             (h : poly_fam (sig_path_param Σ i) F x),
               transport _ (hit_path i x)
               (endpoint_dact hit_point F c (sig_path_lhs Σ i) x h) =
               endpoint_dact hit_point F c (sig_path_rhs Σ i) x h)
      j (t : poly_act (sig_point Σ j) hit_carrier),
      hit_ind F c p (hit_point j t) =
      c j t (poly_dmap (sig_point Σ j) (hit_ind F c p) t) ;

(*
  (* computation rule for paths *)
  hit_path_beta :
    forall (F : hit_carrier -> Type)
      (c : forall i (u : poly_act (sig_point Σ i) hit_carrier),
          poly_fam (sig_point Σ i) F u -> F (hit_point i u))
      (p : forall (i : sig_path_index Σ)
             (x : poly_act (sig_path_param Σ i) hit_carrier)
             (h : poly_fam (sig_path_param Σ i) F x),
               transport _ (hit_path i x)
               (endpoint_dact hit_point F c (sig_path_lhs Σ i) x h) =
               endpoint_dact hit_point F c (sig_path_rhs Σ i) x h)
      (k : sig_path_index Σ) (t : poly_act (sig_path_param Σ k) hit_carrier),
      (* we get a mistmatch here, either something's wrong or we need
         and explicit transport to be inserted. *)
      apD (hit_ind F c p) (hit_path k t) =
      p k t (poly_dmap _ (hit_ind F c p) t)
*)

}.

Arguments hit_point {_ _} _ _.
Arguments hit_path {_ _} _ _.
Arguments hit_ind {_ _} _ _ _ _.

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
    apply (f tt a a).
  - intros F c p [|] [] ; reflexivity.
Defined.

