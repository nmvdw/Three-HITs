(* Double colimits *)

Require Import HoTT HoTT.HIT.Colimits.

Axiom todo : forall A, A.

(** Note: this definition works well when the vertices of [G1] and [G2] are sets.
    We shall add the assumption that they are separately when needed. *)
Definition graph_prod (G1 G2 : graph) : graph :=
  {| graph0 := G1 * G2 ;
     graph1 := (fun u v => (fst u = fst v) * G2 (snd u) (snd v)  + (snd u = snd v) * G1 (fst u) (fst v))
  |}.

Section HIT_colimit_graph.
(** As an example we define the diagram for the construction of HITS.
    We will probably move this section elsewhere. *)

Inductive coeq_graph_vertex := coeq_graph_source | coeq_graph_target.

Inductive coeq_graph_edge := coeq_graph_edge_l | coeq_graph_edge_r.

Definition coeq_graph : graph :=
  {| graph0 := coeq_graph_vertex ;
     graph1 := (fun u v => match u, v with
                           | coeq_graph_source, coeq_graph_target => coeq_graph_edge
                           | _, _ => Empty
                           end)
  |}.

(* [n] is successor of [m]. *)
Fixpoint is_succ (m n : nat) {struct m} : Type :=
  match m, n with
  | 0, S 0 => Unit
  | m' .+1, n' .+1 => is_succ m' n'
  | _, _ => Empty
  end.

Fixpoint succ_is_succ (m : nat) : is_succ m (S m) :=
  match m with
  | 0 => tt
  | S m' => succ_is_succ m'
  end.

Definition telescope_graph : graph :=
  {| graph0 := nat ;
     graph1 := is_succ
  |}.

Definition hit_graph := graph_prod coeq_graph telescope_graph.

Definition truncated_telescope_graph (n : nat) : graph :=
  {| graph0 := { k : nat & k <= n } ;
     graph1 := (fun i j => is_succ i.1 j.1)
  |}.

End HIT_colimit_graph.

Section HIT_colimit_diagram.

Definition HIT_graph_truncated (n : nat) := graph_prod coeq_graph (truncated_telescope_graph n).

Lemma nat_lt_leq {m n : nat} : m < n -> m <= n.
Proof.
  apply todo.
Defined.

Lemma nat_lt_leqS {m n : nat} : m < n -> S m <= n.
  apply todo.
Defined.

(** This structure expresses an intermediate stage of the construction.
    It contains a truncated version of the entire diagram, and commutativity of the squares. *)
Structure HIT_diagram_truncated (n : nat) := {
  hdt_diagram : diagram (HIT_graph_truncated n) ;
  hdt_left_commute :
    forall (k : nat) (k_leq_n : k < n),
      let v1 := (coeq_graph_source, (k; nat_lt_leq k_leq_n)) in
      let v2 := (coeq_graph_target, (k; nat_lt_leq k_leq_n)) in
      let v3 := (coeq_graph_source, (S k; nat_lt_leqS k_leq_n)) in
      let v4 := (coeq_graph_target, (S k; nat_lt_leqS k_leq_n)) in
      let l_k := hdt_diagram _f (inr (idpath, coeq_graph_edge_l) : HIT_graph_truncated n v1 v2) in
      let l_Sk := hdt_diagram _f (inr (idpath, coeq_graph_edge_l) : HIT_graph_truncated n v3 v4) in
      let up_k := hdt_diagram _f (inl (idpath, (succ_is_succ k)) : HIT_graph_truncated n v1 v3) in
      let down_k := hdt_diagram _f (inl (idpath, (succ_is_succ k)) : HIT_graph_truncated n v2 v4) in
      down_k o l_k = l_Sk o up_k ;
  hdt_right_commute :
    forall (k : nat) (k_leq_n : k < n),
      let v1 := (coeq_graph_source, (k; nat_lt_leq k_leq_n)) in
      let v2 := (coeq_graph_target, (k; nat_lt_leq k_leq_n)) in
      let v3 := (coeq_graph_source, (S k; nat_lt_leqS k_leq_n)) in
      let v4 := (coeq_graph_target, (S k; nat_lt_leqS k_leq_n)) in
      let r_k := hdt_diagram _f (inr (idpath, coeq_graph_edge_r) : HIT_graph_truncated n v1 v2) in
      let r_Sk := hdt_diagram _f (inr (idpath, coeq_graph_edge_r) : HIT_graph_truncated n v3 v4) in
      let up_k := hdt_diagram _f (inl (idpath, (succ_is_succ k)) : HIT_graph_truncated n v1 v3) in
      let down_k := hdt_diagram _f (inl (idpath, (succ_is_succ k)) : HIT_graph_truncated n v2 v4) in
      down_k o r_k = r_Sk o up_k
}.
End HIT_colimit_diagram.


