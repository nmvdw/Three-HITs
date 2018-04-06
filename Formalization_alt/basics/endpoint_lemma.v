Require Import HoTT.
Require Import polynomial endpoint.

(* If [h] commutes with constructors, then it commutes with all endpoints. *)
Fixpoint endpoint_dact_compute
         {P Q : polynomial}
         {I : Type}
         {C : I -> polynomial}
         {A : Type}
         {F : A -> Type}
         (c : forall (i : I), poly_act (C i) A -> A)
         (f : forall (i : I) (u : poly_act (C i) A),
             poly_fam (C i) F u -> F (c i u))
         (e : endpoint C P Q)
  : forall (x : poly_act P A)
           (h : forall x, F x)
           (H : forall i u, h (c i u) = f i u (poly_dmap (C i) h u)),
    endpoint_dact c f e x (poly_dmap P h x)
    = poly_dmap Q h (endpoint_act c e x)
  := match e with
     | endpoint_var _ => fun _ _ _ => reflexivity _
     | endpoint_const _ _ t => fun _ _ _ => reflexivity t
     | endpoint_constr _ i e' =>
       fun x h H => let u := (endpoint_act c e' x) in
                    ap (f i u) (endpoint_dact_compute c f e' x h H) @ (H i u)^
     | endpoint_fst _ _ _ e' =>
       fun x h H =>
         ap fst (endpoint_dact_compute c f e' x h H)
     | endpoint_snd _ _ _ e' =>
       fun x h H =>
         ap snd (endpoint_dact_compute c f e' x h H)
     | endpoint_pair _ _ _ e1 e2 =>
       fun x h H =>
         path_prod'
           (endpoint_dact_compute c f e1 x h H)
           (endpoint_dact_compute c f e2 x h H)
     | endpoint_inl _ _ _ e' => endpoint_dact_compute c f e'
     | endpoint_inr _ _ _ e' => endpoint_dact_compute c f e'
     end.

Fixpoint endpoint_act_natural
           {P Q : polynomial}
           {I : Type}
           (C : I -> polynomial)
           (e : endpoint C P Q)
           {X Y : Type}
           (CX : forall (i : I), poly_act (C i) X -> X)
           (CY : forall (i : I), poly_act (C i) Y -> Y)
           (f : X -> Y)
           (Hf : forall (i : I) (x : poly_act (C i) X), f(CX i x) = CY i (poly_map (C i) f x))
  : forall (x : poly_act P X),
    poly_map Q f (endpoint_act CX e x)
    =
    endpoint_act CY e (poly_map P f x)
  := match e with
     | endpoint_var _ =>
       fun x => idpath
     | endpoint_const _ _ _ =>
       fun x => idpath
     | endpoint_constr _ i e =>
       fun x =>
         (Hf i (endpoint_act CX e x))
           @ ap (CY i) (endpoint_act_natural C e CX CY f Hf x)
     | endpoint_fst _ _ _ e =>
       fun x =>
         ap fst (endpoint_act_natural C e CX CY f Hf x)
     | endpoint_snd _ _ _ e =>
       fun x =>
         ap snd (endpoint_act_natural C e CX CY f Hf x)
     | endpoint_pair _ _ _ e₁ e₂ =>
       fun x => path_prod'
                  (endpoint_act_natural C e₁ CX CY f Hf x)
                  (endpoint_act_natural C e₂ CX CY f Hf x)
     | endpoint_inl _ _ _ e =>
       fun x =>
         ap inl (endpoint_act_natural C e CX CY f Hf x)
     | endpoint_inr _ _ _ e =>
       fun x =>
         ap inr (endpoint_act_natural C e CX CY f Hf x)
     end.
