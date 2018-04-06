(* Definition of polynomials. *)
Inductive polynomial :=
  | poly_var : polynomial
  | poly_const : Type -> polynomial
  | poly_times : polynomial -> polynomial -> polynomial
  | poly_plus : polynomial -> polynomial -> polynomial.

Notation "'[-]'" := (poly_var) : poly_scope.
Notation "P * Q" := (poly_times P Q) : poly_scope.
Notation "P + Q" := (poly_plus P Q) : poly_scope.
Notation "'const' C" := (poly_const C) (at level 20) : poly_scope.

Local Open Scope type_scope.

(* The action of a polynomial on a type. *)
Fixpoint poly_act (P : polynomial) (A : Type) :=
  match P with
  | poly_var => A
  | poly_const C => C
  | poly_times Q R => poly_act Q A * poly_act R A
  | poly_plus Q R => poly_act Q A + poly_act R A
  end.

(* The action of a polynomial on a map. *)
Fixpoint poly_map (P : polynomial) {A B : Type} (f : A -> B) :
  poly_act P A -> poly_act P B :=
  match P with
  | poly_var => f
  | poly_const C => (fun x => x)
  | poly_times Q R => (fun x => (poly_map Q f (fst x), poly_map R f (snd x)))
  | poly_plus Q R => (fun u => match u with
                           | inl x => inl (poly_map Q f x)
                           | inr y => inr (poly_map R f y)
                           end)
  end.

(* The action of a polynomial on a type family. *)
Fixpoint poly_fam (P : polynomial) {A : Type} (B : A -> Type) :
  poly_act P A -> Type :=
  match P with
  | poly_var => B
  | poly_const C => (fun _ => C)
  | poly_times Q R => (fun u => poly_fam Q B (fst u) * poly_fam R B (snd u))
  | poly_plus Q R => (fun u => match u with
                           | inl x => poly_fam Q B x
                           | inr y => poly_fam R B y
                           end)
  end.

(* The action of a polynomial on a dependent map. *)
Fixpoint poly_dmap (P : polynomial) {A : Type} {B : A -> Type} (f : forall x, B x) {struct P} :
  forall u : poly_act P A, poly_fam P B u :=
  match P with
  | poly_var => f
  | poly_const C => (fun x => x)
  | poly_times Q R => (fun u => (poly_dmap Q f (fst u), poly_dmap R f (snd u)))
  | poly_plus Q R => (fun u => match u with
                          | inl x => poly_dmap Q f x
                          | inr y => poly_dmap R f y
                          end)
  end.
