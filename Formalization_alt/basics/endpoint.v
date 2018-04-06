Require Import HoTT.
Require Import polynomial.

Section Endpoints.
  (* An endpoint is also called a "constructor term". It is used in
     the HIT signature to describe the endpoints of path constructors.
     Endpoints are parameterized by a family of polynomials which will
     be specialized to the point constructors in the definition of HITs.
   *)
  Variable (I : Type)
           (C : I -> polynomial).

  Inductive endpoint : polynomial -> polynomial -> Type :=
  | endpoint_var :
      forall {P : polynomial},
        endpoint P P
  | endpoint_const :
      forall {P : polynomial} {T : Type},
        T -> endpoint P (poly_const T)
  | endpoint_constr :
      forall {P : polynomial} (i : I),
        endpoint P (C i) -> endpoint P poly_var
  | endpoint_fst :
      forall {P Q R : polynomial},
        endpoint P (poly_times Q R) -> endpoint P Q
  | endpoint_snd :
      forall {P Q R : polynomial},
        endpoint P (poly_times Q R) -> endpoint P R
  | endpoint_pair :
      forall {P Q R : polynomial},
        endpoint P Q -> endpoint P R -> endpoint P (poly_times Q R)
  | endpoint_inl :
      forall {P Q R : polynomial},
        endpoint P Q -> endpoint P (poly_plus Q R)
  | endpoint_inr :
      forall {P Q R : polynomial},
        endpoint P R -> endpoint P (poly_plus Q R).

  Variable (A : Type)
           (F : A -> Type)
           (c : forall (i : I), poly_act (C i) A -> A)
           (f : forall (i : I) (u : poly_act (C i) A), poly_fam (C i) F u -> F (c i u)).

  (* Endpoint acting on data for point constructors. *)
  Fixpoint endpoint_act
           {P Q : polynomial}
           (e : endpoint P Q) (* the endpoint *)
    : poly_act P A -> poly_act Q A
    := match e with
       | endpoint_var _ => idmap
       | endpoint_const _ _ t => fun _ => t
       | endpoint_constr _ i e => fun u => c i (endpoint_act e u) 
       | endpoint_fst _ _ _ e => fun u => fst(endpoint_act e u)
       | endpoint_snd _ _ _ e => fun u => snd(endpoint_act e u)
       | endpoint_pair _ _ _ e1 e2 => fun u => (endpoint_act e1 u, endpoint_act e2 u)
       | endpoint_inl _ _ _ e => fun u => inl(endpoint_act e u)
       | endpoint_inr _ _ _ e => fun u => inr(endpoint_act e u)
       end.

  (* The dependent action of an endpoint, this is used for
     "lifting" the path constructors in the elimination principle. *)
  Fixpoint endpoint_dact
           {P Q : polynomial}
           (e : endpoint P Q)
    : forall (x : poly_act P A), poly_fam P F x -> poly_fam Q F (endpoint_act e x)
    := match e with
       | endpoint_var _ =>
         fun _ h => h
       | endpoint_const _ _ t =>
         fun _ _ => t
       | endpoint_constr _ i u =>
         fun x h =>f i (endpoint_act u x) (endpoint_dact u x h)
       | endpoint_fst p p0 p1 e =>
         fun x h =>fst (@endpoint_dact p (poly_times p0 p1) e x h)
       | endpoint_snd p p0 p1 e =>
         fun x h => snd (@endpoint_dact p (poly_times p0 p1) e x h)
       | endpoint_pair _ _ _ e1 e2 =>
         fun x h => (endpoint_dact e1 x h, endpoint_dact e2 x h)
       | endpoint_inl p p0 _ e =>
         fun x h => @endpoint_dact p p0 e x h
       | endpoint_inr p _ p1 e =>
         fun x h => @endpoint_dact p p1 e x h
       end.

  (* A general HIT might have an arbitrary number of endpoints and therefore an arbitrarily
   nested point constructors. Our construction of a HIT presumes that there is a bound to
   the nesting. We define here what it means for an endpoint to have such a bound. *)
  Inductive endpoint_rank : forall {P Q : polynomial}, endpoint P Q -> nat -> Type :=
  | rank_var :
      forall {P : polynomial} (n : nat),
        endpoint_rank (@endpoint_var P) n
  | rank_const :
      forall {P : polynomial} {T : Type} (t : T) (n : nat),
        endpoint_rank (@endpoint_const P _ t) n
  | rank_constr :
      forall {P : polynomial} (i : I) (n : nat) (e : endpoint P (C i)),
        endpoint_rank e n -> endpoint_rank (endpoint_constr i e) (S n)
  | rank_fst :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P (poly_times Q R)),
        endpoint_rank e n -> endpoint_rank (endpoint_fst e) n
  | rank_snd :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P (poly_times Q R)),
        endpoint_rank e n -> endpoint_rank (endpoint_snd e) n
  | rank_inl :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P Q),
        endpoint_rank e n -> endpoint_rank (@endpoint_inl _ _ R e) n
  | rank_inr :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P R),
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

Arguments endpoint_rank {_} _ {_ _} _ _.