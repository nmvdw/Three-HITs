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

(* There is a cocone over [D] with tip [H]. *)
Lemma cocone_D_H : cocone D H.
Proof.
 simple refine {| q := _ |}.
 + { intros [|].
     - intros jy.
       destruct (@diagram1 _ D true false false jy) as [i x].
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
Defined.

Theorem hit_is_coequalizer `{Funext} : is_colimit D H.
Proof.
  simple refine {| is_colimit_C := _ |}.
  - exact cocone_D_H.
  - { intro Y.
      apply equiv_fcontr_isequiv.
      intro C.
      simple refine {| center := exist _ _ _ |}.
      - simple refine (hit_primrec _ H Y _ _).
        + intros i x u.
          apply (q C false).
          exact (i; x).
        + intros p x u ; simpl.
          refine (transport_const _ _ @ _).
          refine (_ @ (qq C true false false (p;x))^).
          exact (qq C true false true (p;x)).
      - simpl.
        admit.
      - intros [f p].
        admit.
    }
Admitted.

End HIT_is_coequalizer.