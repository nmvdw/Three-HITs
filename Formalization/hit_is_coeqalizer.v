Require Import HoTT HoTT.HIT.Colimits HoTT.HIT.Colimits.Coequalizer.
Require Import polynomial hit_structure.

Definition cocone_eq_q
           {G : graph}
           {D : diagram G}
           {Y : Type}
           {C₁ C₂ : cocone D Y}
           (p : C₁ = C₂)
           {i : G}
           (x : D i)
  : q C₁ i x = q C₂ i x
  := match p with
     | idpath => idpath
     end.

Definition cocone_eq_qq
           {G : graph}
           {D : diagram G}
           {Y : Type}
           {C₁ C₂ : cocone D Y}
           (p : C₁ = C₂)
           {i j : G}
           (g : G i j)
           (x : D i)
  : (qq C₁ i j g x)
        @ (cocone_eq_q p x)
    = (cocone_eq_q p (D _f g x))
        @ qq C₂ i j g x.
Proof.
  induction p ; cbn.
  exact (concat_p1 _ @ (concat_1p _)^).
Defined.
  
(* We show that a HIT is a coequalizer. *)
Section HIT_is_coequalizer.

  (* Suppose we have a hit [H] for a given signature [Σ]. *)
  Variable (Σ : guarded_hit_signature).
  Variable (H : HIT Σ).

  Definition path_left
    : { i : sig_path_index Σ & poly_act (sig_path_param _ i) H }
      -> { i : sig_point_index Σ & poly_act (sig_point _ i) H }
    := fun x =>
         match x with
         | (i;p) => ((guarded_sig_path_lhs Σ i).1;
                       endpoint_act (@hit_point _ H) ((guarded_sig_path_lhs Σ i).2) p)
         end.

  Definition path_right
    : { i : sig_path_index Σ & poly_act (sig_path_param _ i) H }
      -> { i : sig_point_index Σ & poly_act (sig_point _ i) H }
    := fun x =>
         match x with
         | (i;p) => ((guarded_sig_path_rhs Σ i).1;
                       endpoint_act (@hit_point _ H) ((guarded_sig_path_rhs Σ i).2) p)
         end.

  (* We define the diagram for which the HIT is a coequalizer. *)
  Definition D : diagram coequalizer_graph
    := coequalizer_diag path_right path_left.

  (* There is a cocone over [D] with tip [H]. *)
  Lemma cocone_D_H : cocone D H.
  Proof.
    simple refine (Build_coequalizer_cocone (fun p => hit_point p.1 p.2) _).
    exact (fun p => @hit_path Σ H p.1 p.2).
  Defined.

  Definition cocone_map
             {Y : Type}
             (C : cocone D Y)
    : H -> Y.
  Proof.
    refine (hit_primrec Σ H Y (fun i x _ => q C false (i;x)) _).
    intros p x u ; simpl.
    refine (transport_const _ _ @ _).
    exact (qq C true false false (p;x) @ (qq C true false true (p;x))^).
  Defined.

  Definition cocone_map_computation
             `{Funext}
             {Y : Type}
             (C : cocone D Y)
    : postcompose_cocone cocone_D_H (cocone_map C) = C.
  Proof.
    simple refine (path_cocone _ _).
    * intros [ | ].
      ** intros [i x].
         exact (hit_point_primrec_beta _ _ _ _ _ _ _ @ (qq C true false true (i;x))).
      ** intros [i x].
         apply hit_point_primrec_beta.
    * intros [ | ] [ | ] ; simpl ; try contradiction.
      intros [ | ] [i x] ; simpl.
      ** hott_simpl.
      ** rewrite !(hit_path_primrec_beta Σ).
         hott_simpl.
         f_ap.
         rewrite !inv_pp.
         hott_simpl.
  Defined.

  Definition map_eq
             `{Funext}
             {Y : Type}
             (C : cocone D Y)
             (f : H -> Y)
             (Hf : postcompose_cocone cocone_D_H f = C)
             (g : H -> Y)
             (Hg : postcompose_cocone cocone_D_H g = C)
    : f = g.
  Proof.
    apply path_forall.
    simple refine (hit_ind (fun z => f z = g z) _ _).
    - intros i u x.
      refine (@cocone_eq_q _ _ _ _ _ Hf false (i;u) @ _).
      refine (@cocone_eq_q _ _ _ _ _ Hg false (i;u))^.
    - intros j u x ; simpl.
      induction Hf ; simpl.
      hott_simpl.
      unfold postcompose_cocone in Hg.
      refine (transport_paths_FlFr _ _ @ _).
      apply moveR_pM.
      rewrite <- !inv_pp.
      apply ap.
      rewrite <- (@cocone_eq_qq _ _ _ _ _ Hg true false false (j;u)) ; cbn.
      rewrite <- (@cocone_eq_qq _ _ _ _ _ Hg true false true (j;u) @ concat_p1 _).
      cbn.
      hott_simpl.
  Defined.

  Definition ap_map_eq
             `{Funext}
             {Y : Type}
             (C : cocone D Y)
             (f : H -> Y)
             (Hf : postcompose_cocone cocone_D_H f = C)
             (g : H -> Y)
             (Hg : postcompose_cocone cocone_D_H g = C)
    : ap (postcompose_cocone cocone_D_H) (map_eq C f Hf g Hg) = Hf @ Hg^.
  Admitted.

  Definition unique_map
             `{Funext}
             {Y : Type}
             (C : cocone D Y)
    : forall (f g : {a : H -> Y & postcompose_cocone cocone_D_H a = C}), f = g.
  Proof.
    intros [f Hf] [g Hg].
    simple refine (path_sigma' _ _ _).
    - exact (map_eq C f Hf g Hg).
    - rewrite transport_paths_FlFr.
      rewrite ap_const, concat_p1.
      rewrite ap_map_eq.
      rewrite inv_pp, inv_V, concat_pp_p, concat_Vp.
      apply concat_p1.
  Defined.

  Theorem hit_is_coequalizer `{Funext} : is_colimit D H.
  Proof.
    simple refine {| is_colimit_C := _ |}.
    - exact cocone_D_H.
    - intro Y.
      apply equiv_fcontr_isequiv.
      intro C.
      simple refine {| center := exist _ _ _ |}.
      + exact (cocone_map C).
      + exact (cocone_map_computation C).
      + apply (unique_map C).
  Defined.

End HIT_is_coequalizer.