Require Import HoTT.

Require Import polynomial.

Axiom cheating : forall A : Type, A.
Ltac todo := apply cheating.
Axiom magic : forall A B, A -> B.

(* The definition of a HIT signature and a HIT for the signature. *)

(* An endpoint is also called a "constructor term". *)
Inductive endpoint {S : polynomial} : polynomial -> polynomial -> Type :=
  | endpoint_var : forall {P}, endpoint P P
  | endpoint_const : forall {P} {C : Type}, C -> endpoint P (poly_const C)
  | endpoint_constr : forall {P}, endpoint P S -> endpoint P poly_var
  | endpoint_fst : forall {P Q R}, endpoint P (poly_times Q R) -> endpoint P Q
  | endpoint_snd : forall {P Q R}, endpoint P (poly_times Q R) -> endpoint P R
  | endpoint_pair : forall {P Q R}, endpoint P Q -> endpoint P R -> endpoint P (poly_times Q R)
  | endpoint_inl : forall {P Q R}, endpoint P Q -> endpoint P (poly_plus Q R)
  | endpoint_inr : forall {P Q R}, endpoint P R -> endpoint P (poly_plus Q R)
.

(* Endpoint acting on elements. *)
Fixpoint endpoint_act
  {S P Q : polynomial}
  {A : Type}
  (c : poly_act S A -> A)
  (e : @endpoint S P Q)
  {struct e}
  : poly_act P A -> poly_act Q A.
Proof.
  destruct e.

  (* endpoint_var *)
  - exact (fun u => u).

  (* endpoint_const *)
  - exact (fun _ => c0).

  (* endpoint_constr *)
  - exact (fun u => c (endpoint_act _ _ _ _ c e u)).

  (* endpoint_fst *)
  - exact (fun u => fst (endpoint_act _ _ _ _ c e u)).

  (* endpoint_snd *)
  -  exact (fun u => snd (endpoint_act _ _ _ _ c e u)).

  (* endpoint_pair *)
  - exact  (fun u => (endpoint_act _ _ _ _ c e1 u, endpoint_act _ _ _ _ c e2 u)).

  (* endpoint_inl *)
  -  exact (fun u => inl (endpoint_act _ _ _ _ c e u)).

  (* endpoint_inr *)
  -  exact (fun u => inr (endpoint_act _ _ _ _ c e u)).
Defined.

(* A HIT is specified by a single point constructor and a family of path constructors.
   Note: having a single point constructor is as general as having many.
   Note: we are allowing an arbitrary family of path construcrors, and later we will
         require that there is a bound on how deeply the point constructors are nested.
*)
Structure hit_signature := {
  hit_point : polynomial ; (* the signature for a single point constructor *)
  hit_paths_index : Type ; (* indexing for path constructors *)
  hit_paths_param : hit_paths_index -> polynomial ; (* the parameters of each path constructor *)
  hit_paths_lhs : forall i, @endpoint hit_point (hit_paths_param i) poly_var ; (* the left endpoint *)
  hit_paths_rhs : forall i, @endpoint hit_point (hit_paths_param i) poly_var ; (* the right endpoint *)
}.

(* Example: propositional truncation *)
Definition trunc_signature (A : Type) :=
  {|
    hit_point := poly_const A ;
    hit_paths_index := Unit ;
    hit_paths_param := (fun _ => poly_times poly_var poly_var) ;
    hit_paths_lhs := (fun _ => endpoint_fst endpoint_var) ;
    hit_paths_rhs := (fun _ => endpoint_snd endpoint_var)
  |}.

(* Example: circle *)

Definition circle_signature :=
  {|
    hit_point := poly_const Unit ;
    hit_paths_index := Unit ;
    hit_paths_param := (fun _ => poly_const Unit) ;
    hit_paths_lhs := (fun _ => endpoint_constr endpoint_var) ;
    hit_paths_rhs := (fun _ => endpoint_constr endpoint_var)
  |}.

(* Example: susupension *)

Definition suspension_signature (A : Type) :=
  {|
    hit_point := poly_plus (poly_const Unit) (poly_const Unit) ;
    hit_paths_index := Unit ;
    hit_paths_param := (fun _ => poly_const A) ;
    hit_paths_lhs := (fun _ => endpoint_constr (endpoint_inl (endpoint_const tt))) ;
    hit_paths_rhs := (fun _ => endpoint_constr (endpoint_inr (endpoint_const tt)))
  |}.

(* Example: natural numbers *)
Definition nat_signature :=
  {|
    hit_point := poly_plus (poly_const Unit) poly_var ;
    hit_paths_index := Empty ;
    hit_paths_param := Empty_rect _ ;
    hit_paths_lhs := Empty_rect _ ;
    hit_paths_rhs := Empty_rect _
  |}.

(* Given a carrier type [A], we want to explain what the structure
   of a HIT on [A] is. For this purpose we need to define the types
   of the point constructors, the paths, and intro rules, and the
   eliminator. *)

(* We now embark upon defining the elimnator for the given HIT. *)

Structure hit_data (Σ : hit_signature) :=
{
  data_carrier :> Type ; (* the carrier type *)
  data_point : poly_act (hit_point Σ) data_carrier -> data_carrier ; (* the point constructor *)
  data_eq := (* the type of a path constructor parameterized by [Q] with endpoints [e1] and [e2] *)
    (fun (Q : polynomial)
       (e1 e2 : endpoint Q poly_var) =>
       forall (u : poly_act Q data_carrier), endpoint_act data_point e1 u = endpoint_act data_point e2 u) ;
  data_paths : forall i u, endpoint_act data_point (hit_paths_lhs Σ i) u = endpoint_act data_point (hit_paths_rhs Σ i) u
}.

Arguments data_point {_} _ _.
Arguments data_paths {_} _ _ _.

(* Example: the data for nat. *)
Definition nat_data : hit_data nat_signature.
Proof.
  simple refine {| data_carrier := nat |}.
  - exact (fun u => match u with inl _ => 0 | inr n => S n end).
  - intro i ; elim i.
Defined.

(* The lift of an endpoint -- [dact] stands for "dependent action". *)

Fixpoint endpoint_dact
         {P Q R : polynomial}
         {A : Type}
         (c : poly_act P A -> A)
         (F : A -> Type)
         (f : forall u : poly_act P A, poly_fam P F u -> F (c u))
         (e : @endpoint P Q R)
         {struct e} :
  forall (x : poly_act Q A) (h : poly_fam Q F x), poly_fam R F (endpoint_act c e x).
Proof.
  simple refine (
           match e as z in @endpoint _ Q R
                 return (forall (x : poly_act Q A) (h : poly_fam Q F x), poly_fam R F (endpoint_act c z x))
           with
           | endpoint_var _ => _
           | endpoint_const _ _ t => _
           | endpoint_constr _ u => _
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

Definition hit_ind {Σ : hit_signature} (H : hit_data Σ) :=
  forall (F : H -> Type)
    (c : forall u : poly_act (hit_point Σ) H, poly_fam (hit_point Σ) F u -> F (data_point H u))
    (p : forall (i : hit_paths_index Σ)
           (x : poly_act (hit_paths_param Σ i) H)
           (h : poly_fam (hit_paths_param Σ i) F x),
        transport _ (data_paths H i x) (endpoint_dact (data_point H) F c (hit_paths_lhs Σ i) x h) =
        endpoint_dact (data_point H) F c (hit_paths_rhs Σ i) x h
        ),
    (forall x : H, F x).


(* Example: we prove that natural numbers have an eliminator. *)
Lemma nat_ind : hit_ind nat_data.
Proof.
  intros F c p x.
  simpl in *.
  induction x as [| n y].
  - now apply (c (inl tt)).
  - apply (c (inr n)).
    exact y.
Defined.

(* Example: the HoTT library circle has an eliminator. *)
Definition circle_data : hit_data circle_signature.
Proof.
  refine {| data_carrier := S1 ;
            data_point := (fun _ => base) ;
            data_paths := (fun _ _ => _ ) |}.
  exact loop.
Defined.

Lemma circle_ind : hit_ind circle_data.
Proof.
  intros F c f x.
  apply (S1_ind F (c tt tt)), (f tt).
Defined.

(* Example: the HoTT library suspension has an eliminator. *)

Definition suspension_data (A : Type) : hit_data (suspension_signature A).
Proof.
  simple refine {| data_carrier := Susp A |}.
  - intros [_|_] ; [exact North | exact South].
  - intros [] x.
    exact (merid x).
Defined.

Lemma supsension_ind (A : Type) : hit_ind (suspension_data A).
Proof.
  intros F c f x.
  simpl in *.
  apply (Susp_ind F (c (inl tt) tt) (c (inr tt) tt)).
  intro a.
  apply (f tt a a).
Defined.

(* The computation rule for points. *)


End HIT_structure.