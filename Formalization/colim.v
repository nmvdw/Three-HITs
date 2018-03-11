Require Import HoTT HoTT.HIT.Colimits polynomial.

(* Here we collect general facts about HITs in the HoTT library.
   We will then put the generally useful ones into the HoTT library. *)

(* Note: the coequalizers are already around, see
   http://hott.github.io/HoTT/proviola-html/HoTT.HIT.Colimits.Coequalizer.html *)

(* Note: the mapping telescope is already around, see
   https://ncatlab.org/nlab/show/mapping+telescope for naming,
   and http://hott.github.io/HoTT/proviola-html/HoTT.HIT.Colimits.MappingTelescope.html,
   although that file fails to actually define the relevant HIT, it just provides
   the graph for it. Perhaps we should re-define mapping telescopes directly, i.e.,
   just take the development from ColimsLem.v (that one should be broken down into
   seeral pieces.
*)

Lemma wat {A} : A.
Admitted.

(* Move to general.v *)
Lemma ap_f_eq_l
      {A B : Type}
      (f g : A -> B)
      (e : f == g)
      {a b : A}
      (p : a = b)
  : ap f p = e a @ ap g p @ (e b)^.
Proof.
  induction p ; simpl.
  refine (_ @ ap (fun q => q @ _) (concat_p1 _)^).
  apply (concat_pV _)^.
Defined.

Lemma ap_f_eq_r
      {A B : Type}
      (f g : A -> B)
      (e : f == g)
      {a b : A}
      (p : a = b)
  : (e a)^ @ ap f p @ e b = ap g p.
Proof.
  induction p ; simpl.
  refine (ap (fun q => q @ _) (concat_p1 _) @ _).
  apply (concat_Vp _).
Defined.

Definition inv_unique
      {A : Type}
      {a b : A}
      (p q : a = b)
  : p^ = q^ -> p = q
  := fun H => (inv_V p)^ @ (ap _ H) @ inv_V q.

(* We describe colimits over mapping telescopes and we give more direct principles for them.
   We use the general HIT to define colimits.
*)
Section ColimitNatural.
  Variable (F : nat -> Type)
           (f : forall n : nat, F n -> F(S n)).

  Definition colim_N : Type
    := colimit (Build_sequence F f).

  Definition inc (n : nat) (x : F n) : colim_N
    := @colim mappingtelescope_graph (Build_sequence F f) n x.

  Definition com (n : nat) (x : F n)
    : inc (S n) (f n x) = inc n x
    := @colimp mappingtelescope_graph (Build_sequence F f) n (S n) idpath x.

  (* The induction principle *)
  Section Induction.
    Variable (P : colim_N -> Type)
             (Pi : forall (n : nat), forall (x : F n), P (inc n x))
             (Pc : forall (n : nat) (x : F n), (com n x) # Pi (S n) (f n x) = Pi n x).

    Definition colim_N_ind : forall (x : colim_N), P x.
    Proof.
      simple refine (@colimit_ind mappingtelescope_graph (Build_sequence F f) _ Pi _) ; simpl.
      intros i j [ ] x.
      apply Pc.
    Defined.

    Definition colim_N_ind_beta_inc (n : nat) (x : F n)
      : colim_N_ind (inc n x) = Pi n x
      := idpath.

    Definition colim_N_ind_beta_com (n : nat) (x : F n)
      : apD colim_N_ind (com n x) = Pc n x
      := colimit_ind_beta_colimp _ _ _ _ _ _ _.
  End Induction.

  (* The recursion principle *)
  Section Recursion.
    Variable (P : Type)
             (Pi : forall (n : nat), F n -> P)
             (Pc : forall (n : nat) (x : F n), Pi (S n) (f n x) = Pi n x).

    Definition cocone_nat : cocone (Build_sequence F f) P.
    Proof.
      simple refine (Build_cocone _ _).
      - apply Pi.
      - intros i j [ ] x.
        apply Pc.
    Defined.

    Definition colim_N_rec : colim_N -> P
      := @colimit_rec mappingtelescope_graph (Build_sequence F f) P cocone_nat.

    Definition colim_N_rec_beta_inc (n : nat) (x : F n)
      : colim_N_rec (inc n x) = Pi n x
      := idpath.

    Definition colim_N_rec_beta_com (n : nat) (x : F n)
      : ap colim_N_rec (com n x) = Pc n x
      := colimit_rec_beta_colimp P cocone_nat n (n.+1) idpath x.
  End Recursion.
End ColimitNatural.

Arguments inc {_} {_} _ _.
Arguments com {_} {_} _ _.
Arguments colim_N_ind {_} {_} _ _ _ _.
Arguments colim_N_ind_beta_com {_} {_} _ _ _ _ _.
Arguments colim_N_rec {_} {_} _ _ _ _.
Arguments colim_N_rec_beta_com {_} {_} _ _ _ _ _.

(* Every colimit can be constructed via sigma types and coequalizers.
   This holds for arbitrary diagrams.
   More specifically, we show two things.
   First, we show that we can construct a type with the right introduction, elimination, and computation rules.
   This means that from sigma types and coequalizers we can construct colimits of diagrams.
   Secondly, we show that it is isomorphic to the colimit HIT.
*)
Section ColimAsCoeq.
  Variable (G : graph) (D : diagram G).

  Definition total_diagram := {i : G & D i}.
  Definition maps_diagram := {i : G & D i * {j : G & G i j}}.

  Definition ident_left (x : maps_diagram) : total_diagram :=
    match x with
    | (_;(x,(j;g))) => (j;D _f g x)
    end.

  Definition ident_right (x : maps_diagram) : total_diagram :=
    match x with
    | (i;(x,_)) => (i;x)
    end.

  (* We identify `(i;x)` and `(j;D _f g x)` in the sum.
     This means we identify `x` with its image under any arrow.
  *)
  Definition coeq_D : Type := Coeq ident_left ident_right.

  Definition colim_cd (i : G) : D i -> coeq_D
    := fun x => coeq(i;x).

  Definition colimp_cd
             (i j : G) (g : G i j)
             (x : D i)
    : colim_cd j (D _f g x) = colim_cd i x
    := @cp _ _ ident_left ident_right (i;(x,(j;g))).

  Section Induction.
    Variable (P : coeq_D -> Type)
             (p_in : forall (i : G) (x : D i), P (colim_cd i x))
             (p_p : forall (i j : G) (g : G i j) (x : D i),
                 transport P (colimp_cd i j g x) (p_in j ((D _f g) x)) = p_in i x).

    Definition colim_cd_ind : forall (x : coeq_D), P x.
    Proof.
      simple refine (Coeq_ind _ _ _).
      - intros.
        apply p_in.
      - intros.
        apply p_p.
    Defined.

    Definition colim_cd_beta_colim (i : G) (x : D i)
      : colim_cd_ind (colim_cd i x) = p_in i x
      := idpath.

    Definition colim_cd_beta_colimp
               (i j : G) (g : G i j)
               (x : D i)
      : apD colim_cd_ind (colimp_cd i j g x) = p_p i j g x
      := Coeq_ind_beta_cp _ _ _ (i; (x, (j; g))).
  End Induction.

  (* The actual colimit *)
  Definition colim_D : Type := colimit D.

  Definition coeq_to_colim : coeq_D -> colim_D.
  Proof.
    simple refine (Coeq_rec _ _ _).
    - intros [x z].
      apply (colim x z).
    - intros [i [x [j g]]].
      apply (colimp i j g x).
  Defined.

  Definition colim_to_coeq : colim_D -> coeq_D.
  Proof.
    apply colimit_rec.
    simple refine (Build_cocone colim_cd colimp_cd).
  Defined.

  Global Instance colim_to_coeq_equiv : IsEquiv coeq_to_colim.
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - apply colim_to_coeq.
    - simple refine (colimit_ind _ _ _).
      * reflexivity.
      * intros.
        rewrite transport_paths_FlFr.
        rewrite ap_compose.
        rewrite colimit_rec_beta_colimp.
        rewrite (Coeq_rec_beta_cp _ _ _ (i;(x,(j;g)))).
        hott_simpl.
    - simple refine (colim_cd_ind _ _ _).
      * reflexivity.
      * intros.
        simpl.
        rewrite transport_paths_FlFr.
        rewrite ap_compose.
        rewrite (Coeq_rec_beta_cp _ _ _ (i; (x, (j; g)))).
        rewrite colimit_rec_beta_colimp.
        hott_simpl.
 Defined.
End ColimAsCoeq.

(* Given a diagram `D`, we can make a new diagram `P D` by applying `P` at every point.
   For any diagram `D` and polynomial `P` we consider `colimit (P D)` and `P (colimit D)`.
   In general, these are not the same as colimits do not commute with polynomials.
   However, there always is a map `colimit (P D) -> P (colimit D)`.
   There are three cases to consider: `P` could be constant, a sum, or a product.
*)
Section ColimitPolynomial.
  Variable (G : graph).

  Section Constant.
    Definition constant_diagram (A : Type) : diagram G
      := Build_diagram _ (fun _ => A) (fun _ _ _ => idmap).

    Definition constant (A : Type) := colimit (constant_diagram A).

    Definition colimit_to_const (A : Type) : constant A -> A.
    Proof.
      apply colimit_rec.
      simple refine (Build_cocone _ _).
      - apply (fun _ => idmap).
      - reflexivity.
    Defined.
  End Constant.

  Section Sum.
    Variable (D1 D2 : diagram G).

    Definition sum_diagram : diagram G :=
      Build_diagram
        G
        (fun x => diagram0 D1 x + diagram0 D2 x)
        (fun i j g x =>
           match x with
           | inl y => inl (diagram1 D1 g y)
           | inr z => inr (diagram1 D2 g z)
           end
        ).

    Definition colimit_sum := colimit sum_diagram.
    Definition sum_colimit := colimit D1 + colimit D2.

    Definition colimit_to_sum : colimit_sum -> sum_colimit.
    Proof.
      apply colimit_rec.
      simple refine (Build_cocone _ _).
      - intros i x.
        destruct x as [x | y].
        * apply (inl (colim i x)).
        * apply (inr (colim i y)).
      - intros i1 i2 j x.
        destruct x as [x | y] ; simpl.
        * apply ap.
          apply colimp.
        * apply ap.
          apply colimp.
    Defined.
  End Sum.

  Section Product.
    Variable (D1 D2 : diagram G).

    Definition prod_diagram : diagram G
      := Build_diagram
           G
           (fun x => diagram0 D1 x * diagram0 D2 x)
           (fun _ _ g p => (diagram1 D1 g (fst p), diagram1 D2 g (snd p))).

    Definition colimit_prod := colimit prod_diagram.
    Definition prod_colimit := colimit D1 * colimit D2.

    Definition colimit_to_prod : colimit_prod -> prod_colimit.
    Proof.
      apply colimit_rec.
      simple refine (Build_cocone _ _).
      - intros i x.
        apply (colim i (fst x), colim i (snd x)).
      - intros i1 i2 g x ; simpl.
        apply path_prod' ; apply colimp.
    Defined.
  End Product.

  Section Polynomial.
    Variable (D : diagram G).

    Definition poly_diagram (P : polynomial) : diagram G.
    Proof.
      simple refine (Build_diagram _ _ _).
      - intros i.
        apply (poly_act P (D i)).
      - intros i j g.
        apply (poly_map P (D _f g)).
    Defined.

    Definition colimit_poly (P : polynomial) := colimit (poly_diagram P).

    Definition poly_colimit (P : polynomial) := poly_act P (colimit D).

    Definition colimit_to_poly (P : polynomial) : colimit_poly P -> poly_colimit P.
    Proof.
      unfold colimit_poly, poly_colimit.
      induction P as [ | | P1 IHP1 P2 IHP2 | P1 IHP1 P2 IHP2] ; simpl.
      - apply idmap.
      - intros z.
        apply colimit_to_const.
        apply z.
      - pose (f := colimit_to_prod (poly_diagram P1) (poly_diagram P2)).
        pose (g := fun x => (IHP1 (fst x), IHP2 (snd x))).
        apply (g o f).
      - pose (f := colimit_to_sum (poly_diagram P1) (poly_diagram P2)).
        pose (g := fun x => match x with
                            | inl c => inl (IHP1 c)
                            | inr c => inr (IHP2 c)
                            end).
        apply (g o f).
    Defined.
  End Polynomial.
End ColimitPolynomial.

Arguments sum_diagram {_} _ _.
Arguments sum_colimit {_} _ _.
Arguments colimit_sum {_} _ _.
Arguments colimit_to_sum {_} _ _.
Arguments prod_diagram {_} _ _.
Arguments prod_colimit {_} _ _.
Arguments colimit_prod {_} _ _.
Arguments colimit_to_prod {_} _ _.

(* Colimits always commute with taking sums. *)
Section ColimitSum.
  Variable (G : graph)
           (D1 D2 : diagram G).

  Definition sum_to_colimit (x : sum_colimit D1 D2) : colimit_sum D1 D2.
  Proof.
    destruct x as [y | z].
    - simple refine (colimit_rec _ _ y).
      simple refine (Build_cocone _ _).
      * intros i yi.
        apply (colim i).
        apply (inl yi).
      * intros i j g yi.
        simpl.
        refine (colimp i j g (inl yi : sum_diagram D1 D2 i)).
    - simple refine (colimit_rec _ _ z).
      simple refine (Build_cocone _ _).
      * intros i zi.
        apply (colim i).
        apply (inr zi).
      * intros i j g zi.
        apply (colimp i j g (inr zi : sum_diagram D1 D2 i)).
  Defined.

  Lemma sum_colim_sum : forall (x : sum_colimit D1 D2),
      colimit_to_sum D1 D2 (sum_to_colimit x) = x.
  Proof.
    destruct x as [y | z].
    - simple refine (colimit_ind (fun z => _) _ _ y).
      * reflexivity.
      * intros.
        rewrite transport_paths_FlFr.
        rewrite ap_compose.
        rewrite colimit_rec_beta_colimp.
        rewrite (colimit_rec_beta_colimp _ _ _ _ _ (inl x : sum_diagram D1 D2 i)).
        hott_simpl.
    - simple refine (colimit_ind (fun z => _ = _) _ _ z).
      * reflexivity.
      * intros.
        rewrite transport_paths_FlFr.
        rewrite ap_compose.
        rewrite colimit_rec_beta_colimp.
        rewrite (colimit_rec_beta_colimp _ _ _ _ _ (inr x : sum_diagram D1 D2 i)).
        hott_simpl.
  Defined.

  Lemma colim_sum_colim : forall (x : colimit_sum D1 D2),
      sum_to_colimit(colimit_to_sum D1 D2 x) = x.
  Proof.
    simple refine (colimit_ind _ _ _) ; simpl.
    - intros.
      destruct x as [y| z] ; reflexivity.
    - intros.
      rewrite transport_paths_FlFr.
      rewrite ap_compose.
      destruct x as [y | y]; rewrite concat_p1.
      * rewrite (colimit_rec_beta_colimp _ _ _ _ _ (inl y : sum_diagram D1 D2 i)).
        rewrite <- (ap_compose inl).
        rewrite colimit_rec_beta_colimp.
        hott_simpl.
      * rewrite (colimit_rec_beta_colimp _ _ _ _ _ (inr y : sum_diagram D1 D2 i)).
        rewrite <- (ap_compose inr).
        rewrite colimit_rec_beta_colimp.
        hott_simpl.
  Defined.

  Global Instance colimit_to_sum_equiv : IsEquiv (colimit_to_sum D1 D2).
  Proof.
    apply isequiv_biinv.
    split ; exists sum_to_colimit ; intro x.
    - apply colim_sum_colim.
    - apply sum_colim_sum.
  Defined.
End ColimitSum.

(* Colimits do not commute with products and constant diagrams, but they do if certain conditions hold on the graph.
   These are `nonempty` (there is a node), `thin` (there is at most one vertex between every two nodes, and `filtered` (each two nodes has an upper bound).
   For products, we need `thin` and `filtered, and for constant diagrams we also need `nonempty`.
*)
Section GraphDefinitions.
  (* `connected i j` says there is a path from `i` to `j`.
     A path is just a list of connected vertices.
  *)
  Inductive connected {G : graph} : G -> G -> Type :=
  | G_nil : forall i, connected i i
  | G_cons : forall i j k, G i j -> connected j k -> connected i k.

  Fixpoint compose
             {G : graph} {i j k : G}
             (p1 : connected i j)
    : connected j k -> connected i k
    := match p1 with
       | G_nil _ => fun p2 => p2
       | G_cons k1 k2 k3 g p1 => fun p2 => G_cons k1 k2 k g (compose p1 p2)
       end.

  (* The relevant graph properties *)
  Definition nonempty (G : graph) := G.

  Class is_simple_graph (G : graph) :=
    connect_hprop : forall (i j : G), IsHProp (connected i j).

  Definition filtered (G : graph) :=
    forall (x y : G), {z : G & connected x z /\ connected y z}.

  (* Vertices in graphs give arrows in diagrams.
     Paths in graphs give compositions in diagrams.
  *)
  Fixpoint compose_long
           {G : graph} {i j : G} (D : diagram G) (p : connected i j)
    : D i -> D j
    := match p with
       | G_nil _ => idmap
       | G_cons _ _ _ g q => (compose_long D q) o (D _f g)
       end.

  Notation "D '_fp' g" := (compose_long D g) (at level 8).

  Definition compose_long_add
             {G : graph} (D : diagram G)
             {i j k1 k2 : G} (g : G i j)
             (Hjk1 : connected j k1) (Hk1k2 : connected k1 k2)
             (x : D i)
    : D _fp (compose Hjk1 Hk1k2) ((D _f g) x)
      =
      D _fp (compose (G_cons _ _ _ g Hjk1) Hk1k2) x
    := idpath.

  Definition double_compose_long
             {G : graph} {i j k : G} (D : diagram G)
             (Hij : connected i j) (Hjk : connected j k)
             (x : D i)
    : D _fp Hjk (D _fp Hij x) = D _fp (compose Hij Hjk) x.
  Proof.
    induction Hij as [ | ? ? ? ? ? H] ; simpl.
    - reflexivity.
    - apply H.
  Defined.

  Fixpoint colimp_p
             {G : graph} {i j : G} {D : diagram G} (H : connected i j)
    : forall (x : D i), colim j (compose_long D H x) = colim i x
    := match H with
       | G_nil _ => fun _ => idpath
       | G_cons _ _ _ g q => fun x => colimp_p q _ @ colimp _ _ g x
       end.

  Definition colimp_p_compose
             {G : graph} {i j k : G} (D : diagram G)
             (Hij : connected i j) (Hjk : connected j k)
             (x : D i)
    : colim k (D _fp (compose Hij Hjk) x) = colim i x
    := ap (colim k) (double_compose_long D Hij Hjk x)^ @ colimp_p Hjk _ @ colimp_p Hij x.

  Definition double_colimp_p
             {G : graph} {i j k : G} (D : diagram G)
             (Hij : connected i j) (Hjk : connected j k)
             (x : D i)
    : colimp_p (compose Hij Hjk) x = colimp_p_compose D Hij Hjk x.
  Proof.
    unfold colimp_p_compose.
    induction Hij as [ | ? ? ? ? ? H] ; simpl.
    - refine ((concat_1p _)^ @ (concat_p1 _)^).
    - refine (ap (fun z => z @ _) (H Hjk _) @ concat_pp_p _ _ _).
  Defined.

  Definition colimp_p_e
             {G : graph} {i j : G} (D : diagram G) (H : connected i j)
    : (fun x => colim j (D _fp H x)) == colim i
    := colimp_p H.

  Definition level_compose
             {G : graph} {i k1 k2 : G} (D : diagram G)
             (Hik1 : connected i k1) (Hk1k2 : connected k1 k2)
             (x : D i)
    : colim k2 (D _fp Hk1k2 (D _fp Hik1 x)) = colim k2 (D _fp (compose Hik1 Hk1k2) x).
  Proof.
    apply ap.
    apply double_compose_long.
  Defined.

  Definition colimp_compose
             {G : graph} {i k1 k2 : G} (D : diagram G)
             (Hik1 : connected i k1) (Hk1k2 : connected k1 k2)
             (x : D i)
    : colimp_p Hk1k2 (D _fp Hik1 x) @ colimp_p Hik1 x
      = level_compose D Hik1 Hk1k2 x @ colimp_p (compose Hik1 Hk1k2) x.
  Proof.
    induction Hik1.
    - refine (concat_p1 _ @ (concat_1p _)^).
    - simpl.
      rewrite concat_p_pp.
      rewrite IHHik1.
      hott_simpl.
  Defined.
End GraphDefinitions.

Arguments G_cons {_} {_} {_} {_} _ _.
Notation "D '_fp' g" := (compose_long D g) (at level 8).

(* The mapping telescope graph is rather nice: it is `is_simple_graph`, `filtered`, and `nonempty`.
   We show the former two properties.
*)
Section MappingTelescopeGraph.
  (* Some general lemmata on natural numbers. *)
  Definition subn0 {n : nat} : n - 0 = n
    := match n with
       | 0 => idpath
       | S _ => idpath
       end.

  Fixpoint leq_S (n : nat) : n <= (S n)
    := match n with
       | 0 => tt
       | S n' => leq_S n'
       end.

  Definition leq_or {n : nat}
    : forall {m : nat}, n <= (m.+1) -> (n <= m) + (n = m.+1).
  Proof.
    induction n as [ | n IHn].
    - intros.
      apply (inl tt).
    - destruct m.
      * intros H.
        unfold leq in H ; simpl in H.
        refine (inr (ap S _)).
        apply equiv_path_nat.
        rewrite subn0 in H.
        apply H.
      * intros H1.
        destruct (IHn _ H1) as [t | t].
        ** apply (inl t).
        ** apply (inr (ap S t)).
  Defined.

  Definition leq_not {m : nat}
    : forall {n : nat}, ~(n <= m) -> m <= n.
  Proof.
    induction m as [ | m IHm].
    - refine (fun _ _ => tt).
    - simpl in *.
      induction n.
      * intros f.
        contradiction (f tt).
      * intros H.
        apply (IHm n (fun Hn => H Hn)).
  Defined.

  Lemma S_inj {n m : nat} (H : S n = S m) : n = m.
  Proof.
    pose (code_nat n.+1 m.+1) as d.
    pose (x := equiv_path_nat^-1 H : d).
    simpl in d.
    apply (equiv_path_nat x).
  Defined.

  Definition leq_discrete {i j k} (p : k = i.+1)
    : i <= j -> j <= k -> (j = i) + (j = k).
  Proof.
    rewrite p. clear p. clear k.
    revert i.
    induction j as [ | j IHj].
    - simpl.
      intros i H1 H2.
      destruct i.
      * apply (inl idpath).
      * apply (Empty_rec H1).
    - induction i.
      * simpl in *.
        intros H1 H2.
        refine (inr (ap S _)).
        induction j.
        ** reflexivity.
        ** apply (Empty_rec H2).
      * intros H1 H2.
        destruct (IHj i H1 H2) as [p | p].
        ** apply (inl (ap S p)).
        ** apply (inr (ap S p)).
  Defined.

  Definition max (n m : nat) : nat
    := match (dec (n <= m)) with
       | inl _ => m
       | inr _ => n
       end.

  Definition max_l : forall n m, n <= (max n m).
  Proof.
    intros ; unfold max.
    destruct (dec (n <= m)) as [t | t] ; simpl.
    - apply t.
    - apply leq_refl.
  Defined.

  Definition max_r : forall n m, m <= (max n m).
  Proof.
    intros ; unfold max.
    destruct (dec (n <= m)) as [t | t] ; simpl.
    - apply leq_refl.
    - apply (leq_not t).
  Defined.

  (* We first show `connected i j` iff `i <= j` *)
  Definition G_succ (j : mappingtelescope_graph)
    : connected j j.+1.
  Proof.
    refine (G_cons _ (G_nil _)).
    reflexivity.
  Defined.

  Definition connected_mtg_to_leq {i j : mappingtelescope_graph}
    : connected i j -> i <= j.
  Proof.
    induction 1 as [ | ? ? ? g X IHX].
    - apply leq_refl.
    - simpl in *.
      refine (leq_trans _ _ _ (leq_S _) _).
      rewrite g.
      apply IHX.
  Defined.

  Definition leq_to_connected_mtg
    : forall {i j : mappingtelescope_graph}, i <= j -> connected i j.
  Proof.
    destruct i ; induction j as [ | j IHj].
    - intros.
      apply G_nil.
    - intros.
      simpl in *.
      refine (compose (IHj tt) _).
      apply G_succ.
    - simpl in *.
      contradiction.
    - intros H.
      destruct (leq_or H) as [t | t].
      * refine (compose (IHj t) _).
        apply G_succ.
      * rewrite t.
        apply G_nil.
  Defined.

  (* Now we can show the diagram is filtered *)
  Definition filtered_mtg : filtered mappingtelescope_graph.
  Proof.
    unfold filtered, mappingtelescope_graph ; simpl.
    intros i j.
    exists (max i j).
    split ; apply leq_to_connected_mtg.
    - apply max_l.
    - apply max_r.
  Defined.

  (* Showing it is is_simple_graph, requires more work.
     We need some lemmata to show that each `y : connected i i` is equal to `G_nil i`.
  *)
  Definition connected_mtg_ii_fam (i j : mappingtelescope_graph) (z : connected i j) : Type.
  Proof.
    destruct (dec (i = j)).
    - induction p.
      refine (G_nil i = z).
    - apply True.
  Defined.

  Lemma connected_mtg_ii_lem i j z : connected_mtg_ii_fam i j z.
  Proof.
    simple refine (connected_rect _ connected_mtg_ii_fam _ _ _ _ _).
    - intros.
      unfold connected_mtg_ii_fam.
      destruct (dec (i0 = i0)).
      * assert (p = idpath) as X.
        { apply path_ishprop. }
        rewrite X.
        reflexivity.
      * apply tt.
    - intros i0 j0 k g ? X.
      unfold connected_mtg_ii_fam.
      destruct (dec (i0 = k)).
      * induction p.
        simpl in *.
        pose (connected_mtg_to_leq c) as t.
        rewrite <- g in t.
        refine (Empty_rec _).
        clear X. clear c. clear g.
        induction i0 as [ | ? H].
        ** apply t.
        ** apply H.
           apply t.
      * apply tt.
  Defined.

  Lemma connected_mtg_ii (i : mappingtelescope_graph) y : G_nil i = y.
  Proof.
    generalize (connected_mtg_ii_lem i i y).
    unfold connected_mtg_ii_fam.
    destruct (dec (i = i)).
    * assert (p = idpath) as X.
      { apply path_ishprop. }
      rewrite X.
      apply idmap.
    * contradiction (n idpath).
  Defined.

  Global Instance is_simple_graph_mtg : is_simple_graph mappingtelescope_graph.
  Proof.
    intros i j.
    apply hprop_allpath.
    intros x y.
    induction x as [ | i j k g ?].
    - simpl in *.
      apply connected_mtg_ii.
    - destruct y as [ | ? ? ? g0 ?].
      * simpl in *.
        refine (Empty_rec _).
        clear IHx.
        rewrite <- g in x.
        assert (i.+1 <= i) as X.
        { apply (connected_mtg_to_leq x). }
        clear g. clear x.
        induction i as [ | i IHi].
        ** apply X.
        ** refine (IHi X).
      * simpl in *.
        induction g, g0.
        f_ap.
  Defined.
End MappingTelescopeGraph.

(* For filtered colimits, we need several operations moving elements into a higher stage.
   These operations need to be well-defined meaning that it does not depend on the stage.
*)
Section FilteredColimits.
  Variable (G : graph) (D : diagram G).

  Definition transport_up
             (Y : colimit D -> Type)
             {i k : G} (x : D i)
             (Hik : connected i k)
             (p : Y(colim k (D _fp Hik x)))
    : Y(colim i x)
    := transport Y (colimp_p Hik _) p.

  Definition go_up
             (Y : colimit D -> Type)
             {i k1 k2 : G} (x : D i)
             (Hik1 : connected i k1) (Hk1k2 : connected k1 k2)
             (p : Y(colim k1 (D _fp Hik1 x)))
    : Y (colim k2 (D _fp (compose Hik1 Hk1k2) x)).
  Proof.
    refine (transport _ _ p).
    simple refine ((colimp_p Hk1k2 _)^ @ _).
    apply ap.
    apply double_compose_long.
  Defined.

  Definition transport_up_well_def
             (Y : colimit D -> Type)
             {i k1 k2 : G} (x : D i)
             (Hik1 : connected i k1)
             (Hk1k2 : connected k1 k2)
             (p : Y(colim k1 (D _fp Hik1 x)))
    : transport_up Y x Hik1 p = transport_up Y x (compose Hik1 Hk1k2) (go_up Y x Hik1 Hk1k2 p).
  Proof.
    unfold go_up, transport_up.
    refine (_ @ transport_pp _ _ _ _).
    refine (ap (fun z => transport Y z p) _).
    induction Hik1 as [ | ? ? ? ? ? IH] ; simpl.
    - refine ((concat_Vp _)^ @ (ap (fun z => z @ _) (concat_p1 _))^).
    - refine (_ @ concat_pp_p _ _ _).
      refine (ap (fun z => z @ _) (IH _ Hk1k2 p)).
  Defined.

  Definition choose_top
             {i j k : G} (x : D i) (y : D j)
             (Hik : connected i k) (Hjk : connected j k)
             (p : D _fp Hik x = D _fp Hjk y)
    : colim i x = colim j y
    := transport_up _ _ Hjk ((colimp_p Hik _)^ @ ap (colim k) p).

  Theorem choose_top_well_def
          (i j k1 k2 : G) (x : D i) (y : D j)
          (Hik1 : connected i k1) (Hjk1 : connected j k1)
          (Hk1k2 : connected k1 k2)
          (p : D _fp Hik1 x = D _fp Hjk1 y)
          (q : D _fp (compose Hik1 Hk1k2) x
               = D _fp (compose Hjk1 Hk1k2) y)
          (h : (double_compose_long D Hik1 Hk1k2 x)^
               @ (ap D _fp Hk1k2 p @ double_compose_long D Hjk1 Hk1k2 y)
               = q)
    : choose_top x y Hik1 Hjk1 p
      =
      choose_top x y (compose Hik1 Hk1k2) (compose Hjk1 Hk1k2) q.
  Proof.
    simple refine (transport_up_well_def _ _ _ Hk1k2 _ @ _).
    unfold choose_top, transport_up, go_up.
    rewrite !transport_paths_FlFr.
    hott_simpl.
    rewrite (ap_f_eq_l (colim k1) _ (fun x => (colimp_p_e _ Hk1k2 x)^)).
    rewrite inv_V.
    rewrite concat_pp_p.
    rewrite ap_compose.
    hott_simpl.
    rewrite <- inv_pp.
    repeat f_ap.
    rewrite !concat_pp_p.
    rewrite <- ap_pp.
    unfold colimp_p_e.
    rewrite colimp_compose.
    rewrite inv_pp.
    rewrite !concat_pp_p.
    f_ap.
    unfold level_compose.
    rewrite <- ap_V.
    rewrite <- ap_pp.
    refine (ap _ _).
    refine (concat_p_pp _ _ _ @ _).
    apply h.
  Defined.

  Definition choose_top_inv
             {i j k : G} (x : D i) (y : D j)
             (Hik : connected i k) (Hjk : connected j k)
             (p : D _fp Hik x = D _fp Hjk y)
    : (choose_top x y Hik Hjk p)^ = choose_top y x Hjk Hik p^.
  Proof.
    unfold choose_top, transport_up.
    rewrite !transport_paths_FlFr.
    rewrite !inv_pp.
    hott_simpl.
  Defined.

  Definition choose_top_concat
             {i j1 k j2 : G} (x1 : D i) (y1 : D j1) (y2 : D j2)
             (Hik : connected i k) (Hj1k : connected j1 k) (Hj2k : connected j2 k)
             (p1 : D _fp Hik x1 = D _fp Hj1k y1)
             (p2 : D _fp Hj1k y1 = D _fp Hj2k y2)
    : (choose_top x1 y1 Hik Hj1k p1) @ (choose_top y1 y2 Hj1k Hj2k p2)
      = (choose_top x1 y2 Hik Hj2k (p1 @ p2)).
  Proof.
    unfold choose_top, transport_up.
    rewrite !transport_paths_FlFr.
    rewrite ap_pp.
    hott_simpl.
  Defined.

  (*
  Definition choose_top_concat_diff
             {i j1 k1 k2 k3 j2 : G} (x1 : D i) (y1 : D j1) (y2 : D j2)
             (Hik1 : path i k1) (Hj1k1 : path j1 k1)
             (Hj1k2 : path j1 k2) (Hj2k2 : path j2 k2)
             (Hk1k3 : path k1 k3) (Hk2k3 : path k2 k3)
             (p1 : D _fp (inl Hik1) x1 = D _fp (inl Hj1k1) y1)
             (p2 : D _fp (inl Hj1k2) y1 = D _fp (inl Hj2k2) y2)
             q
    : (choose_top x1 y1 (inl Hik1) (inl Hj1k1) p1) @ (choose_top y1 y2 (inl Hj1k2) (inl Hj2k2) p2)
      =
      choose_top x1 y2 (inl (G_compose Hik1 Hk1k3)) (inl (G_compose Hj2k2 Hk2k3)) q.
  Proof.
    assert (D _fp (inl (G_compose Hik1 Hk1k3)) x1 = D _fp (inl (G_compose Hj2k2 Hk2k3)) y2).
    {
      simpl.
      refine (ap _ p1 @ _).
      refine (_ @ ap _ p2).
      rewrite !double_compose_long.
      f_ap.
      admit.
    }
  Admitted.*)
End FilteredColimits.

Arguments transport_up {G D} Y {i k} _ _ _.
Arguments transport_up_well_def {G D} Y {i k1 k2} x Hik1 Hk1k2 p.
Arguments choose_top {G D i j k} x y Hik Hjk _.
Arguments choose_top_well_def {G D i j k1 k2} x y Hik1 Hjk1 Hk1k2 p q.

(* If the graph is `is_simple_graph`, `filtered`, and `nonempty`, then colimits over it commute with the constant functor.
*)
Section ColimConst.
  Variable (G : graph) (g : nonempty G) (G_fil : filtered G)
           (A : Type).
  Context `{is_simple_graph G}.

  (* We start by defining the inverse *)
  Definition const_to_colimit (a : A) : constant G A
    := @colim G (constant_diagram G A) g a.

  (* To prove these maps are indeed ivnerses, we need to lift elements to a higher level.
     The operations all need to be well defined.
     In addition, we compute how paths act on elements in the diagram.
  *)
  Definition compose_long_const (x : A) (i j : G) (Hij : connected i j)
    : (constant_diagram G A) _fp Hij x = x.
  Proof.
    induction Hij as [ | ? ? ? ? ? IH].
    - reflexivity.
    - apply IH.
  Defined.

  Definition compose_const
             {k1 k2} (Hk1k2 : connected k1 k2)
    : (constant_diagram G A) _fp Hk1k2 == idmap.
  Proof.
    induction Hk1k2 as [ | ? ? ? ? ? IH] ; simpl.
    * intro z. reflexivity.
    * intros z. apply IH.
  Defined.

  Definition choose_top_const
        {i j k : G} (x : A)
        (Hik : connected i k) (Hjk : connected j k)
    : @colim G (constant_diagram G A) i x = @colim G (constant_diagram G A) j x.
  Proof.
    simple refine (choose_top _ _ Hik Hjk _).
    refine (compose_long_const _ _ _ _ @ (compose_long_const _ _ _ _)^).
  Defined.

  Definition choose_top_well_def_const
        {i j k1 k2 : G} (x : A)
        (Hik1 : connected i k1) (Hjk1 : connected j k1)
        (Hk1k2 : connected k1 k2)
    : choose_top_const x Hik1 Hjk1
      =
      choose_top_const x (compose Hik1 Hk1k2) (compose Hjk1 Hk1k2).
  Proof.
    simple refine (choose_top_well_def _ _ _ _ _ _ _ _).
    induction Hik1 ; simpl.
    - rewrite !concat_1p.
      induction Hjk1.
      * induction Hk1k2.
        ** reflexivity.
        ** apply IHHk1k2.
      * apply IHHjk1.
    - apply IHHik1.
  Defined.

  Definition choose_top_colimp
        (g' i1 i2 j : G)
        (Hgj : connected g j)
        (Hi2j : connected i2 j)
        (x : A)
        (g12 : G i1 i2)
    : (choose_top_const x Hgj Hi2j)
        @
        @colimp G (constant_diagram G A) i1 i2 g12 x
      =
      choose_top_const x Hgj (compose (G_cons g12 (G_nil _)) Hi2j).
  Proof.
    unfold choose_top_const, choose_top, transport_up.
    rewrite !transport_paths_FlFr.
    rewrite !concat_pp_p.
    rewrite !ap_const.
    hott_simpl.
  Defined.

  Global Instance colimit_to_const_equiv : IsEquiv (colimit_to_const G A).
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - apply const_to_colimit.
    - intro x.
      reflexivity.
    - simple refine (colimit_ind _ _ _).
      * intros i x ; simpl in *.
        unfold const_to_colimit.
        destruct (G_fil i g) as [k [Hik Hgk]].
        apply (choose_top_const x Hgk Hik).
      * intros i j gij x ; simpl.
        rewrite transport_paths_FlFr.
        rewrite ap_compose.
        rewrite (colimit_rec_beta_colimp _ _ i j gij x).
        simpl.
        rewrite concat_1p, ap_idmap.
        destruct (G_fil j g) as [k1 [Hjk1 Hgk1]] ; simpl.
        destruct (G_fil i g) as [k2 [Hik2 Hgk2]] ; simpl.
        destruct (G_fil k1 k2) as [k3 [Hk1k3 Hk2k3]].
        rewrite (choose_top_well_def_const x Hgk1 Hjk1 Hk1k3).
        rewrite (choose_top_well_def_const x Hgk2 Hik2 Hk2k3).
        rewrite (choose_top_colimp g i j).
        repeat f_ap ; apply connect_hprop.
  Defined.
End ColimConst.

(* To show filtered colimits commute with products, we first prove a double recursion pricniple for colimits. *)
Section ColimitDoubleRecursion.
  Variable (G : graph) (D1 D2 : diagram G).

  Definition colimit_rec2
             (Y : Type)
             (f : forall i j, D1 i -> D2 j -> Y)
             (f_l : forall i j1 j2 g x y, f i j2 x ((D2 _f g) y) = f i j1 x y)
             (f_r : forall i1 i2 j g1 x y,  f i2 j ((D1 _f g1) x) y = f i1 j x y)
             (f_coh : forall i1 i2 j1 j2 g1 g2 x y,
                 ((f_l i2 j1 j2 g2 ((D1 _f g1) x) y)^
                  @ f_r i1 i2 j2 g1 x ((D2 _f g2) y))
                   @ f_l i1 j1 j2 g2 x y
                 =
                 f_r i1 i2 j1 g1 x y)
    : colimit D1 * colimit D2 -> Y.
  Proof.
    intros [xf yf].
    simple refine (colimit_rec _ _ xf).
    simple refine (Build_cocone _ _).
    - intros i x.
      simple refine (colimit_rec _ _ yf).
      simple refine (Build_cocone _ _).
      * intros j y.
        apply (f i j x y).
      * intros j1 j2 g y ; simpl.
        apply f_l.
    - intros i1 i2 g1 x ; simpl.
      revert yf.
      simple refine (colimit_ind _ _ _).
      * intros j y ; simpl.
        apply f_r.
      * intros j1 j2 g2 y ; simpl.
        rewrite transport_paths_FlFr.
        rewrite !colimit_rec_beta_colimp ; simpl.
        apply f_coh.
  Defined.
End ColimitDoubleRecursion.

Section ColimitProduct.
  Variable (G : graph)
           (D1 D2 : diagram G)
           (G_fil : filtered G).
  Context `{is_simple_graph G}.

  Definition compose_long_prod
             {i j : G} (Hij : connected i j) (x : prod_diagram D1 D2 i)
    : (prod_diagram D1 D2) _fp Hij x
      =
      (D1 _fp Hij (fst x), D2 _fp Hij (snd x)).
  Proof.
    induction Hij as [ | ? ? ? ? ? IH].
    - reflexivity.
    - apply IH.
  Defined.

  Definition choose_top_prod {i j : G} (x : D1 i) (y : D2 j) : colimit_prod D1 D2.
  Proof.
    destruct (G_fil i j) as [k [Hik Hjk]].
    apply (colim k).
    apply (D1 _fp Hik x, D2 _fp Hjk y).
  Defined.

  Definition prod_diag_fp_l
             (i1 i2 j k1 k2 k3 : G)
             (g1 : G i1 i2)
             (x : D1 i1)
             (y : D2 j)
             (Hi1k1 : connected i1 k1)
             (Hjk1 : connected j k1)
             (Hi2k2 : connected i2 k2)
             (Hjk2 : connected j k2)
             (Hk1k3 : connected k1 k3)
             (Hk2k3 : connected k2 k3)
    : (prod_diagram D1 D2) _fp Hk2k3 (D1 _fp Hi2k2 ((D1 _f g1) x), D2 _fp Hjk2 y) =
      (prod_diagram D1 D2) _fp Hk1k3 (D1 _fp Hi1k1 x, D2 _fp Hjk1 y).
  Proof.
    refine (compose_long_prod _ _ @ _ @ (compose_long_prod _ _)^).
    apply path_prod'.
    * simpl.
      refine (double_compose_long _ _ _ _ @ _).
      refine (_ @ (double_compose_long _ _ _ _)^).
      refine (compose_long_add _ _ _ _ _ @ _).
      refine (ap (fun z => D1 _fp z x) _).
      apply connect_hprop.
    * refine (double_compose_long _ _ _ _ @ _ @ (double_compose_long _ _ _ _)^).
      refine (ap (fun z => D2 _fp z y) _).
      apply connect_hprop.
  Defined.

  Definition prod_diag_fp_r
             {i j1 j2 k1 k2 k3 : G}
             (g : G j1 j2)
             (x : D1 i)
             (y : D2 j1)
             (Hik1 : connected i k1)
             (Hj1k1 : connected j1 k1)
             (Hik2 : connected i k2)
             (Hj2k2 : connected j2 k2)
             (Hk1k3 : connected k1 k3)
             (Hk2k3 : connected k2 k3)
    : (prod_diagram D1 D2) _fp Hk2k3 (D1 _fp Hik2 x, D2 _fp Hj2k2 ((D2 _f g) y)) =
      (prod_diagram D1 D2) _fp Hk1k3 (D1 _fp Hik1 x, D2 _fp Hj1k1 y).
  Proof.
    refine (compose_long_prod _ _ @ _ @ (compose_long_prod _ _)^).
    apply path_prod'.
    * simpl.
      refine (double_compose_long _ _ _ _ @ _ @ (double_compose_long _ _ _ _)^).
      refine (ap (fun z => D1 _fp z x) _).
      apply connect_hprop.
    * simpl.
      refine (double_compose_long _ _ _ _ @ _).
      refine (compose_long_add _ _ _ _ _ @ _).
      refine (_ @ (double_compose_long _ _ _ _)^).
      refine (ap (fun z => D2 _fp z y) _).
      apply connect_hprop.
  Defined.

  Definition choose_top_prod_l
             (i1 i2 j : G)
             (g1 : G i1 i2)
             (x : D1 i1)
             (y : D2 j)
    : choose_top_prod ((D1 _f g1) x) y = choose_top_prod x y.
  Proof.
    unfold choose_top_prod.
    destruct (G_fil i1 j) as [k1 [Hi1k1 Hjk1]].
    destruct (G_fil i2 j) as [k2 [Hi2k2 Hjk2]].
    destruct (G_fil k1 k2) as [k3 [Hk1k3 Hk2k3]].
    simple refine (choose_top _ _ Hk2k3 Hk1k3 _).
    apply prod_diag_fp_l.
  Defined.

  Definition choose_top_prod_r
             (i j1 j2 : G)
             (g : G j1 j2)
             (x : D1 i)
             (y : D2 j1)
    : choose_top_prod x ((D2 _f g) y) = choose_top_prod x y.
  Proof.
    unfold choose_top_prod.
    destruct (G_fil i j1) as [k1 [Hik1 Hj1k1]].
    destruct (G_fil i j2) as [k2 [Hik2 Hj2k2]].
    destruct (G_fil k1 k2) as [k3 [Hk1k3 Hk2k3]].
    simple refine (choose_top _ _ Hk2k3 Hk1k3 _).
    apply prod_diag_fp_r.
  Defined.

  Definition prod_to_colimit : prod_colimit D1 D2 -> colimit_prod D1 D2.
  Proof.
    simple refine (colimit_rec2 G D1 D2 _ _ _ _ _) ; simpl.
    - apply @choose_top_prod.
    - apply choose_top_prod_r.
    - apply choose_top_prod_l.
    - intros i1 i2 j1 j2 g1 g2 x y.
      unfold choose_top_prod_l, choose_top_prod_r.
      rewrite choose_top_inv.
      apply wat.
  Defined.

  Global Instance colimit_to_prod_equiv : IsEquiv (colimit_to_prod D1 D2).
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - apply prod_to_colimit.
    - intros [x y].
      simple refine (colimit_ind (fun z => _) _ _ x).
      * intros i xi.
        simple refine (colimit_ind (fun z => _) _ _ y).
        ** intros j yj ; simpl.
           destruct (G_fil i j) as [k [Hik Hjk]].
           apply path_prod' ; apply colimp_p.
        ** intros j1 j2 g yj1 ; simpl.
           rewrite transport_paths_FlFr.
           rewrite ap_compose.
           rewrite colimit_rec_beta_colimp.
           simpl.
           apply wat.
      * intros i1 i2 g x1.
        simple refine (colimit_ind (fun z => _) _ _ y).
        ** intros j yj ; cbn.
           rewrite transport_paths_FlFr.
           rewrite ap_compose.
           apply wat.
        ** intros j1 j2 g12 yj ; cbn.
           apply wat.
    - intros x ; simpl.
      simple refine (colimit_ind (fun z => _) _ _ x).
      * intros i xi ; simpl.
        simple refine (choose_top _ _ _ _ _).
        ** apply (G_fil i (G_fil i i).1).
        ** apply (G_fil i (G_fil i i).1).2.
        ** apply (G_fil i (G_fil i i).1).2.
        ** simpl.
           apply wat.
      * intros i j g xi.
        rewrite transport_paths_FlFr.
        simpl.
        rewrite ap_idmap.
        rewrite ap_compose.
        rewrite (colimit_rec_beta_colimp _ _ i j g xi) ; simpl.
        hott_simpl.
        simpl.
        apply wat.
  Defined.
End ColimitProduct.

(* Now we can show colimits over `filtered`, `is_simple_graph`, `nonempty` graphs commute with polynomials. *)
Section FilteredColimitPolynomial.
  Variable (G : graph)
           (g : nonempty G)
           (G_fil : filtered G).
  Context `{is_simple_graph G}.

  Global Instance colimit_to_poly_equiv (D : diagram G) P
    : IsEquiv (colimit_to_poly G D P).
  Proof.
    induction P.
    - apply _.
    - unfold colimit_to_poly ; simpl.
      apply (colimit_to_const_equiv G g G_fil T).
    - refine isequiv_compose.
      apply (colimit_to_prod_equiv G (poly_diagram G D P1) (poly_diagram G D P2) G_fil).
    - refine isequiv_compose.
      apply (colimit_to_sum_equiv G (poly_diagram G D P1) (poly_diagram G D P2)).
  Defined.
End FilteredColimitPolynomial.

(* We specialize this result to colimits over the `mappingtelescope_graph`. *)
Section ColimitNPolynomial.
  Definition poly_act_fam_N
             (P : polynomial)
             (F : nat -> Type)
             (n : nat)
    := poly_act P (F n).

  Definition poly_act_map_N
             (P : polynomial)
             (F : nat -> Type) (f : forall n, F n -> F n.+1)
    : forall (n : nat), poly_act_fam_N P F n -> poly_act_fam_N P F n.+1
    := fun n => poly_map P (f n).

  Definition colimit_N_poly
             (P : polynomial)
             (F : nat -> Type) (f : forall n, F n -> F n.+1)
    : colim_N (poly_act_fam_N P F) (poly_act_map_N P F f) -> poly_act P (colim_N F f).
  Proof.
    intros X.
    apply colimit_to_poly.
    unfold colimit_poly.
    simple refine (colim_N_rec _ _ _ X).
    - intros i x.
      simple refine (colim _ _).
      * apply i.
      * apply x.
    - intros n x ; simpl.
      apply (@colimp mappingtelescope_graph
                     (poly_diagram mappingtelescope_graph (Build_sequence F f) P)
                     n n.+1 idpath x).
  Defined.

  Global Instance colimit_N_poly_commute
         (P : polynomial)
         (F : nat -> Type) (f : forall n, F n -> F n.+1)
    : IsEquiv (colimit_N_poly P F f).
  Proof.
    refine isequiv_compose.
    - simple refine (isequiv_adjointify _ _ _ _).
      * apply colimit_rec.
        simple refine (Build_cocone _ _).
        ** intros n x.
           simpl in *.
           apply (inc n x).
        ** intros n m g x.
           simpl in *.
           induction g.
           apply (@com _ (fun n => poly_map P (f n)) n x).
      * simple refine (colimit_ind _ _ _).
        ** intros i x ; simpl in *.
           reflexivity.
        ** intros i j g x.
           induction g.
           rewrite transport_paths_FlFr.
           rewrite ap_compose.
           rewrite colimit_rec_beta_colimp.
           simpl.
           hott_simpl.
           rewrite (colim_N_rec_beta_com _ _ _ i x).
           hott_simpl.
      * simple refine (colim_N_ind _ _ _).
        ** intros n x ; simpl in *.
           reflexivity.
        ** intros n x ; simpl in *.
           rewrite transport_paths_FlFr.
           rewrite ap_compose.
           rewrite colim_N_rec_beta_com.
           hott_simpl.
           rewrite ap_V.
           rewrite (@colimit_rec_beta_colimp
                      mappingtelescope_graph
                      (poly_diagram mappingtelescope_graph (Build_sequence F f) P)
                      _ _ n n.+1 idpath x).
           hott_simpl.
    - apply (colimit_to_poly_equiv mappingtelescope_graph 0 filtered_mtg).
  Defined.
End ColimitNPolynomial.