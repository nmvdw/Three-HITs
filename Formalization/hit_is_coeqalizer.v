Require Import HoTT HoTT.HIT.Colimits HoTT.HIT.Colimits.Coequalizer.
Require Import polynomial hit_structure.

(* We show that a HIT is a coequalizer. *)
Section HIT_is_coequalizer.

(* Suppose we have a hit [H] for a given signature [Σ]. *)
Variable (Σ : guarded_hit_signature).
Variable (H : HIT Σ).

(* We define the diagram for which the HIT is a coequalizer. *)
Definition D : diagram coequalizer_graph.
Proof.
  simple refine {| diagram0 :=
                     (fun (b : coequalizer_graph)  => match b with
                            | true => { i : sig_path_index Σ & poly_act (sig_path_param _ i) H }
                            | false  => { i : sig_point_index Σ & poly_act (sig_point _ i) H }
                            end)
                |}.
  - intros [|] [|] e ; try elim e.
    destruct e as [|].
    + intros [i p].
      exists ((guarded_sig_path_lhs Σ i).1).
      exact (endpoint_act (@hit_point _ H) ((guarded_sig_path_lhs Σ i).2) p).
    + intros [i p].
      exists ((guarded_sig_path_rhs Σ i).1).
      exact (endpoint_act (@hit_point _ H) ((guarded_sig_path_rhs Σ i).2) p).
Defined.

Theorem hit_is_coequalizer : is_colimit D H.
Proof.
  simple refine {| is_colimit_C := _ |}.
  - simple refine {| q := _ |}.
    + { intros [|].
        - pose (l := @diagram1 _ D true false false).
          intros jy.
          destruct (l jy) as [i x].
          exact (@hit_point Σ H i x).
        - intros [i x].
          exact (@hit_point Σ H i x).
      }
    + { simpl.
        intros [|] [|] e ; try elim e.
        destruct e as [|].
        - intros [i x].
          apply (@hit_path Σ H i).
        - reflexivity.
      }
  - intro Y.
    admit.
Admitted.


End HIT_is_coequalizer.