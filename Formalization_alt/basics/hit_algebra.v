Require Import HoTT.
Require Import polynomial endpoint functor polynomial_lemma.

(* A HIT signature is specified by point constructors and path constructors.

   Note: we are allowing an arbitrary family of poitn and path construcrors.
         We will restrict them later on in existence theorem.

   A guarded HIT is a HIT in which all endpoints are constructors.
 *)
Structure hit_signature :=
  {
    (* indexing for point constructors *)
    sig_point_index : Type ;

    (* the signatures for point constructors *)
    sig_point : sig_point_index -> polynomial ;

    (* indexing for path constructors *)
    sig_path_index : Type ;

    (* the parameters of each path constructor *)
    sig_path_param : sig_path_index -> polynomial ;

    (* the left and right endpoints of path constructors *)
    sig_path_lhs : forall (j : sig_path_index),
        { c : sig_point_index &
              endpoint sig_point
                       (sig_path_param j)
                       (sig_point c) } ;
    sig_path_rhs : forall (j : sig_path_index),
        { c : sig_point_index &
              endpoint sig_point
                       (sig_path_param j)
                       (sig_point c) }
  }.

Section point_constr_functor.
  Variable (Σ : hit_signature).
  
  Definition point_constr (X : Type)
    := {i : sig_point_index Σ & poly_act (sig_point Σ i) X}.

  Definition point_constr_fmap {X Y : Type} (f : X -> Y)
    : point_constr X -> point_constr Y
    := fun x => (x.1;poly_map (sig_point Σ x.1) f x.2).

  Global Instance point_constr_functor `{Funext} : functor point_constr.
  Proof.
    unshelve esplit.
    - exact @point_constr_fmap.
    - unfold point_constr_fmap.
      intros X.
      funext x.
      apply (path_sigma' _ idpath).
      exact (poly_map_id (sig_point Σ x.1) x.2).
    - unfold point_constr_fmap.
      intros X Y Z f g.
      funext x.
      apply (path_sigma' _ idpath).
      exact (poly_map_compose (sig_point Σ x.1) f g x.2).
  Defined.

  Definition point_constr_map
             {X : Type}
             (cX : forall (i : sig_point_index Σ),
                 poly_act (sig_point Σ i) X -> X)
    : point_constr X -> X
    := fun z =>
         match z with
         | (i;x) => cX i x
         end.
End point_constr_functor.

Section path_constr_functor.
  Variable (Σ : hit_signature).
  
  Definition path_param
    := fun X => {j : sig_path_index Σ & poly_act (sig_path_param Σ j) X}.

  Definition path_param_fmap {X Y : Type} (f : X -> Y)
    : path_param X -> path_param Y
    := fun x => (x.1;poly_map (sig_path_param Σ x.1) f x.2).

  Global Instance path_param_functor `{Funext} : functor path_param.
  Proof.
    unshelve esplit.
    - exact @path_param_fmap.
    - unfold path_param_fmap.
      intros X.
      funext x.
      apply (path_sigma' _ idpath).
      exact (poly_map_id (sig_path_param Σ x.1) x.2).
    - unfold point_constr_fmap.
      intros X Y Z f g.
      funext x.
      apply (path_sigma' _ idpath).
      exact (poly_map_compose (sig_path_param Σ x.1) f g x.2).
  Defined.
End path_constr_functor.
  
Definition path_lhs
           {Σ : hit_signature}
           {X : Type}
           (cX : forall (i : sig_point_index Σ),
               poly_act (sig_point Σ i) X -> X)
           (x : path_param Σ X)
  : point_constr Σ X
  := ((sig_path_lhs Σ x.1).1;endpoint_act cX (sig_path_lhs Σ x.1).2 x.2).

Definition path_rhs
           {Σ : hit_signature}
           {X : Type}
           (cX : forall (i : sig_point_index Σ),
               poly_act (sig_point Σ i) X -> X)
           (x : path_param Σ X)
  : point_constr Σ X
  := ((sig_path_rhs Σ x.1).1;endpoint_act cX (sig_path_rhs Σ x.1).2 x.2).

Record hit_algebra (Σ : hit_signature) :=
  {
    alg_carrier : Type ;
    alg_point : forall (i : sig_point_index Σ),
        poly_act (sig_point Σ i) alg_carrier -> alg_carrier ;
    alg_cmap :
        Coeq (path_lhs alg_point) (path_rhs alg_point)
        ->
        alg_carrier ;
    alg_commute : forall (x : point_constr Σ alg_carrier),
        alg_cmap (coeq x)
        =
        point_constr_map Σ alg_point x
  }.

Definition build_hit_algebra
           (Σ : hit_signature)
           (A : Type)
           (cA : forall (i : sig_point_index Σ),
               poly_act (sig_point Σ i) A -> A)
           (pA : forall (j : sig_path_index Σ) (x : poly_act (sig_path_param Σ j) A),
               cA (sig_path_lhs Σ j).1 (endpoint_act cA (sig_path_lhs Σ j).2 x)
               =
               cA (sig_path_rhs Σ j).1 (endpoint_act cA (sig_path_rhs Σ j).2 x)
           )
  : hit_algebra Σ.
Proof.
  simple refine {|alg_carrier := A ; alg_point := cA|}.
  - simple refine (Coeq_rec _ (point_constr_map Σ cA) _).
    exact (fun b => pA b.1 b.2).
  - reflexivity.
Defined.

Arguments alg_carrier {Σ} _.
Arguments alg_point {Σ} _ _ _.
Arguments alg_cmap {Σ} _ _.
Arguments alg_commute {Σ} _ _.

Definition alg_path
           {Σ : hit_signature}
           (A : hit_algebra Σ)
           (x : path_param Σ (alg_carrier A))
  : point_constr_map (alg_point A) (path_lhs (alg_point A) x)
    =
    point_constr_map (alg_point A) (path_rhs (alg_point A) x)
  := (alg_commute A _)^ @ ap (alg_cmap A) (cp x) @ alg_commute A _.
