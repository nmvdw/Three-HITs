Require Import HoTT.
Require Import polynomial.
Require Import hit_structure.
Require Import colim.
Require Import pcoeq.

(* We formulate the main theorem, which states that all signatures have a HIT provided that several HITs do.
   We assume function extensionality, which we use to prove
   `inc seq constr_seq_map n.+2
    =
    inc seq constr_seq_map n.+3 o constr_seq_map n.+2`
   This requires function extensionality since `com` only gives the equality for all points.
   Function extensionality can be avoided by using 'strong colimits' where the path `com` has the type `forall n, inc n = inc n.+1 o f n`.
*)
Section hit_existence.
  Context `{Funext}.
  Variable (Σ : hit_signature).
  
  (* To build the approximating sequence, we first need to be able to construct types in which the endpoints of Σ can be interpreted.
     For the Three-HITs theorem we assume all endpoints have at most depth `n`, so it suffices to interpret endpoints of depth `n`.
     We first define a type `Hcon A n` in which endpoints of depth `n` with parameters in `A` can be interpreted.
     In addition, we show that whenever we have a map `Hcon A n -> B`, then in `B`, we can interpret endpoints of depth `n` with parameters from `A` as well.
  *)
  Section add_constructors.
    Fixpoint Hcon (n : nat) (A : Type) : Type :=
      match n with
      | 0 => A
      | S n => A + {i : sig_point_index Σ & poly_act (sig_point Σ i) (Hcon n A)}
      end.

    (* `Hcon n` acts on maps. *)
    Fixpoint Hcon_map {A B : Type} (n : nat) (f : A -> B) : Hcon n A -> Hcon n B
      := match n with
         | 0 => f
         | S n =>
           fun x =>
             match x with
             | inl x => inl(f x)
             | inr (i;x) => inr(i;poly_map (sig_point Σ i) (Hcon_map n f) x)
             end
         end.

    (* Inclusions of `A` into `Hcon n` *)
    Definition Hcon_inA {A : Type} {n : nat} : A -> Hcon n A :=
      match n with
      | 0 => idmap
      | S n => inl
      end.

    (* Interpretation of constructors in `Hcon (n.+1)` with arguments from `A` *)
    Definition Hcon_constr
               {A : Type} {n : nat}
               (i : sig_point_index Σ) (x : poly_act (sig_point Σ i) A)
      : Hcon (n.+1) A
      := inr(i;poly_map (sig_point Σ i) Hcon_inA x).

    (* Intepretation of constructors in `Hcon (n.+1)` with arguments from `Hcon n A` *)
    Definition Hcon_C
               {A : Type} {n : nat}
               {i : sig_point_index Σ} (x : poly_act (sig_point Σ i) (Hcon n A))
      : Hcon (n.+1) A
      := inr(i;x).

    (* Endpoints of rank `n` can be interpreted in `Hcon A` *)
    Fixpoint interpret_endpoint
             {A : Type} {P Q : polynomial} {n : nat}
             (e : endpoint (sig_point Σ) P Q)
             (H : endpoint_rank (sig_point Σ) e n)
      : poly_act P A -> poly_act Q (Hcon n A)
      := match H with
         | rank_var P _ => poly_map P Hcon_inA
         | rank_const _ _ t _ => fun _ => t
         | rank_constr _ _ _ e H => fun x => Hcon_C (interpret_endpoint e H x)
         | rank_fst _ _ _ _ e H => fun x => fst(interpret_endpoint e H x)
         | rank_snd _ _ _ _ e H => fun x => snd(interpret_endpoint e H x)
         | rank_inl _ _ _ _ e H => fun x => inl(interpret_endpoint e H x)
         | rank_inr _ _ _ _ e H => fun x => inr(interpret_endpoint e H x)
         end.

    (* Endpoints of rank `n` can be interpreted in `B` given `Hcon A -> B` *)
    Definition interpret_endpoint_all
               {A B : Type} {P Q : polynomial} {n : nat}
               (e : endpoint (sig_point Σ) P Q)
               (H : endpoint_rank (sig_point Σ) e n)
               (f : Hcon n A -> B) (x : poly_act P A)
      : poly_act Q B
      := poly_map Q f (interpret_endpoint e H x).

    (* Next we show that interpreting endpoints is natural.
       First, we show that `Hcon_inA` is a natural transformation.
     *)
    Definition Hcon_inA_natural
          {A B : Type} {n : nat}
          (f : A -> B)
      : Hcon_inA o f = Hcon_map n f o Hcon_inA
      := match n with
         | 0 => idpath
         | S n => idpath
         end.

    (* Move to polynomial.v. This says `poly_map` commutes with composition. *)
    Definition poly_map_compose
               {A B C : Type} {P : polynomial}
               (f : A -> B) (g : B -> C) (x : poly_act P A)
      : poly_map P g (poly_map P f x) = poly_map P (g o f) x.
    Proof.
      induction P as [ | | ? IHP1 ? IHP2 | ? IHP1 ? IHP2 ] ; simpl.
      - reflexivity.
      - reflexivity.
      - rewrite IHP1, IHP2. reflexivity.
      - destruct x ; rewrite IHP1 || rewrite IHP2 ; reflexivity.
    Defined.
    
    (* Before showing interpreting endpoints is natural, we need one more lemma. *)
    Lemma poly_map_Hcon_inA
          {A B : Type} {P : polynomial} {n : nat}
          (f : A -> B) (x : poly_act P A)
      : poly_map P Hcon_inA (poly_map P f x)
        =
        poly_map P (Hcon_map n f) (poly_map P Hcon_inA x).
    Proof.
      refine (poly_map_compose _ _ _ @ _ @ (poly_map_compose _ _ _)^).
      refine (ap (fun f => f x) _).
      refine (ap (poly_map P) _).
      apply Hcon_inA_natural.
    Defined.

    Definition interpret_natural
               {A B : Type} {P Q : polynomial} {n : nat}
               (e : endpoint (sig_point Σ) P Q)
               (H : endpoint_rank (sig_point Σ) e n)
               (f : A -> B) (x : poly_act P A)
      : interpret_endpoint e H ((poly_map P f) x)
        =
        poly_map Q (Hcon_map n f) (interpret_endpoint e H x).
    Proof.
      induction H as
          [ | | ? ? ? ? ? IHe | ? ? ? ? ? ? IHe | ? ? ? ? ? ? IHe
            | ? ? ? ? ? ? IHe | ? ? ? ? ? ? IHe] ; simpl.
      - apply poly_map_Hcon_inA.
      - reflexivity.
      - refine (ap Hcon_C (IHe x)).
      - refine (ap fst (IHe x)).
      - refine (ap snd (IHe x)).
      - refine (ap inl (IHe x)).
      - refine (ap inr (IHe x)).
    Defined.

    (* The map `interpret_endpoint_all` is natural as well.
       For this we need an extra coherency as given in `coh`.
    *)
    Definition interpret_all_natural
               {A B C D : Type} {P : polynomial} {n : nat}
               (e : endpoint (sig_point Σ) P poly_var)
               (H : endpoint_rank (sig_point Σ) e n)
               (f : Hcon n A -> B)
               (g : Hcon n B -> C)
               (h : C -> D)
               (x : poly_act P A)
               (coh : forall p,
                   h (g (Hcon_inA (f p)))
                   =
                   h (g (Hcon_map n (f o Hcon_inA) p))
               )
      : h ((g o Hcon_inA) (interpret_endpoint_all e H f x))
        =
        h (interpret_endpoint_all e H g (poly_map P (f o Hcon_inA) x))
      := coh (interpret_endpoint e H x)
             @ ap h (ap g (interpret_natural e H (f o Hcon_inA) x)^).

    (* Coherency relating `Hcon_inA` and `Hcon_map` *)
    Definition coherency_map_in {Q R : Type} n (f : Hcon (n.+1) R -> Q) (x : R) :
      Hcon_inA (f (inl x)) = Hcon_map n (f o inl) (Hcon_inA x)
      := match n with
         | 0 => reflexivity _
         | S n => idpath
         end.
  End add_constructors.

  (* Now let us assume the HIT has a certain rank `r.+1`. *)
  Variable (r : nat) (H : hit_rank Σ r.+1).

    (* We start by defining what an approximating sequence for `Σ` is and for that, we follow the ideas in Adamek's theorem.
     At every stage new constructors are added.
     For the path constructors, we need to be able to use constructor terms and that is where `Hcon` comes into play.
     This leads to the notion of `step_data`.
     However, to guarantee the colimit is indeed a HIT for `Σ`, the constructors needs to be added in a coherent way.
     We give several invariants which can directly be used to prove the colimit satisfies the requirements for being a HIT for `Σ`.
     To make the development more modular, we use type classes for the invariants.
  *)
  Section approximating_sequence.
    (* We have stages `P` and `Q` (these represent `F(n.+1)` and `F n` respectively).
       The constructors of the HIT with arguments in `Q`, should be interpreted in `P`.
       This gives a constructor `constrH` for the points and a constructor `path` for the paths.
    *)
    Class step_data (P Q : Type) :=
      {
        constrH : Hcon (r.+1) Q -> P ;
        path : forall (i : sig_path_index Σ)
                      (x : poly_act (sig_path_param Σ i) Q),
            interpret_endpoint_all (sig_path_lhs Σ i) (fst H i) constrH x
            =
            interpret_endpoint_all (sig_path_rhs Σ i) (snd H i) constrH x
      }.

    Arguments constrH {_} {_} _ _.
    Arguments path {_} {_} _ _ _.

    (* A constructor sequence is a sequence with `step_data` at every stage. *)
    Class constr_seq (F : nat -> Type)
      := constr : forall (n : nat), step_data (F(n.+1)) (F n).
    
    (* We work with an arbitrary constructor sequence in the remainder of this section. *)
    Variable (seq : nat -> Type).
    Context `{constr_seq seq}.

    (* In order to take the colimit, we need maps `F n -> F(n.+1)`.
       These can be built from `step_data`.
       This is the composition `F n -> Hcon (F n) -> F(n.+1)`.
       The first map is the inclusion `Hcon_inA` and the second map `constrH`.
       So, we first make step data inclusions `sd_i` and then the maps of the sequence.
    *)
    Definition sd_i {P Q : Type} (Hstep : step_data P Q) : Q -> P
      := constrH Hstep o Hcon_inA.

    Definition constr_seq_map (n : nat) : seq n -> seq (n.+1)
      := sd_i (constr n).

    (* Now we define a candidate for the HIT. *)
    Definition colim_constr_seq := colim_N seq constr_seq_map.

    (* From `step_data`, we define the point and path constructors. *)
    Definition point_constr
               (n : nat) (i : sig_point_index Σ)
               (x : poly_act (sig_point Σ i) (seq n))
      := constrH (constr n) (Hcon_constr i x).

    Definition path_constr
               (n : nat) (i : sig_path_index Σ)
               (x : poly_act (sig_path_param Σ i) (seq n))
      : interpret_endpoint_all (sig_path_lhs Σ i) (fst H i) (constrH (constr n)) x
        =
        interpret_endpoint_all (sig_path_rhs Σ i) (snd H i) (constrH (constr n)) x
      := path (constr n) i x.

    (* Next we need to show this type is indeed a HIT for `Σ`.
       For this, the sequence needs to satisfy several coherencies.
    *)
    Section coherencies.
      (* The coherency for the points says that `point_constr` is a natural transformation from `poly_act (sig_point Σ i) seq` to `seq`.
         We have this coherency for all levels `n`, indices `i`, and arguments `x`.
      *)
      Section pt_intro_coh.
        Variable (n : nat) (i : sig_point_index Σ)
                 (x : poly_act (sig_point Σ i) (seq n)).

        Definition pt_coh_left : seq (n.+2)
          := point_constr (n.+1) i (poly_map (sig_point Σ i) (constr_seq_map n) x).

        Definition pt_coh_right : seq (n.+2)
          := constr_seq_map (n.+1) (point_constr n i x).
      End pt_intro_coh.      

      Class point_intro_coherent :=
        pt_coh :
            forall (n : nat) (i : sig_point_index Σ)
                   (x : poly_act (sig_point Σ i) (seq n)),
              pt_coh_left n i x = pt_coh_right n i x.

      (* If we want to talk about path constructors, we first need to be able to interpret endpoints in the type.
          For the endpoints, the coherencies say that it does not matter whether we interpret it on level `n` or level `n+1`.
          This gives two extra coherencies: one for the left and one for the right.
          The endpoint coherencies are for all endpoints, so we take an arbitrary level `n`, index `i`, and parameter `x`. 
      *)
      Section endpoint_coh.
        Variable (n : nat) (i : sig_path_index Σ)
                 (x : poly_act (sig_path_param Σ i) (seq n)).

        Definition endpointl_coh_left
          := interpret_endpoint_all
               (sig_path_lhs Σ i)
               (fst H i)
               (constrH (constr n.+1))
               (poly_map (sig_path_param Σ i) (constr_seq_map n) x).

        Definition endpointl_coh_right
          := constr_seq_map
               n.+1
               (interpret_endpoint_all (sig_path_lhs Σ i) (fst H i) (constrH (constr n)) x).

        Definition endpointr_coh_left
          := interpret_endpoint_all
               (sig_path_rhs Σ i)
               (snd H i)
               (constrH (constr n.+1))
               (poly_map (sig_path_param Σ i) (constr_seq_map n) x).

        Definition endpointr_coh_right
          := constr_seq_map
               n.+1
               (interpret_endpoint_all (sig_path_rhs Σ i) (snd H i) (constrH (constr n)) x).
      End endpoint_coh.

      Class endpoint_coherent :=
        {
          endpointl_coh :
            forall (n : nat) (i : sig_path_index Σ)
                   (x : poly_act (sig_path_param Σ i) (seq n)),
              endpointl_coh_left n i x = endpointl_coh_right n i x ;
          endpointr_coh :
            forall (n : nat) (i : sig_path_index Σ)
                   (x : poly_act (sig_path_param Σ i) (seq n)),
              endpointr_coh_left n i x = endpointr_coh_right n i x
        }.

      (* For the paths, we also need coherencies.
         To formulate these, we need that the sequence is `endpoint_coherent`.
         The coherency holds for arbitrary levels `n`, indices `i`, and parameters `x`.
         Basically, this says that interpreting the path constructor on level `n` and `n+1` is the same.
         However, the endpoints of the two paths are not definitionally equal, so we use the endpoint coherencies to compare them.
         Furthermore, the paths are only required to be equal in the stage `n+2`, so we apply `ap (constr_seq_map n.+2)` to it.
      *)
      Section pth_intro_coh.
        Variable (n : nat) (i : sig_path_index Σ)
                 (x : poly_act (sig_path_param Σ i) (seq n)).
        Context `{endpoint_coherent}.
        
        Definition path_coherent_left :=
          ap (constr_seq_map n.+2)
             ((endpointl_coh n i x)^
              @ (path_constr
                   n.+1 i
                   (poly_map (sig_path_param Σ i) (constr_seq_map n) x)
                   @ endpointr_coh n i x)).

        Definition path_coherent_right :=
          ap (constr_seq_map n.+2) (ap (constr_seq_map n.+1) (path_constr n i x)).
       End pth_intro_coh.

      Class path_intro_coherent `{endpoint_coherent} :=
        pth_coh : forall (n : nat) (i : sig_path_index Σ)
                         (x : poly_act (sig_path_param Σ i) (seq n)),
          path_coherent_left n i x = path_coherent_right n i x.
    End coherencies.

    (* If the sequence is `point_intro_coherent`, then the introduction rule for the point constructor holds.
       We start by defining the sequence `point_constr_seq` which is `(sig_point Σ i)` applied to `seq n` at every level `n`.
       The point introduction rule maps from the colimit of this sequence to the colimit of the constructor sequence.
    *)
    Section pt_intro.
      Variable (i : sig_point_index Σ).
      Context `{point_intro_coherent}.

      (* The colimit sequence of the arguments of the point constructor. *)
      Definition point_constr_seq (n : nat) := poly_act (sig_point Σ i) (seq n).
      Definition point_constr_map (n : nat) := poly_map (sig_point Σ i) (constr_seq_map n).      
      Definition colim_point_constr_seq := colim_N point_constr_seq point_constr_map.

      Theorem pt_intro : colim_point_constr_seq -> colim_constr_seq.
      Proof.
        simple refine (colim_N_rec _ _ _ _ _).
        - simpl ; intros n x.
          apply (inc _ _ (n.+1) (point_constr _ i x)).
        - simpl ; intros n x.
          refine (ap _ _ @ com _ _ _ _).
          apply pt_coh.
      Defined.
    End pt_intro.

    (* Before we show the introduction rule for the paths, we need to lift the endpoints.
       We do this for arbitrary indices `i`.
    *)
    Section lift_endpoints.
      Variable (i : sig_path_index Σ).
      Context `{endpoint_coherent}.

      (* The colimit sequence of the parameters of the path constructors. *)
      Definition path_constr_seq (n : nat)
        := poly_act (sig_path_param Σ i) (seq n).
      Definition path_constr_seq_map (n : nat)
        := poly_map (sig_path_param Σ i) (constr_seq_map n).      
      Definition colim_path_constr_seq
        := colim_N path_constr_seq path_constr_seq_map.

      Definition endpoint_lhs : colim_path_constr_seq -> colim_constr_seq.
      Proof.
        simple refine (colim_N_rec _ _ _ _ _).
        - simpl ; intros n x.
          apply (inc _ _ (n.+1)).
          refine (interpret_endpoint_all (sig_path_lhs Σ i) (fst H i) (constrH (constr _)) x).
        - simpl ; intros n x.
          refine (_ @ com _ _ _ _).
          refine (ap (inc seq constr_seq_map n.+2) _).
          apply endpointl_coh.
      Defined.

      Definition endpoint_rhs : colim_path_constr_seq -> colim_constr_seq.
      Proof.
        simple refine (colim_N_rec _ _ _ _ _).
        - simpl ; intros n x.
          apply (inc _ _ (n.+1)).
          refine (interpret_endpoint_all (sig_path_rhs Σ i) (snd H i) (constrH (constr _)) x).
        - simpl ; intros n x.
          refine (_ @ com _ _ _ _).
          refine (ap (inc seq constr_seq_map n.+2) _).
          apply endpointr_coh.
      Defined.
    End lift_endpoints.
    
    (* If the sequence is `path_intro_coherent`, then we can prove the introduction rule for the paths. *)
    Section pth_intro.
      Context `{endpoint_coherent} `{path_intro_coherent}.

      (* Move to colimit. *)
      (* Computation of `ap (inc F f (k.+1)) p`. *)
      Definition ap_inc
                 (F : nat -> Type) (f : forall n, F n -> F n.+1)
                 (k : nat) (x y : F k.+1) (p : x = y)
        : (com F f (k.+1) x)^
          @ ap (inc F f (k.+2)) (ap (f (k.+1)) p)
            @ com F f (k.+1) y
          = ap (inc F f (k.+1)) p
        := match p with
           | idpath => ap (fun z => z @ _) (concat_p1 _) @ concat_Vp _
           end.

      (* Move to colimit. *)
      (* With functional extensionaltiy, `com` gives an equality of functions. *)
      Definition strong_com
                 (F : nat -> Type) (f : forall n, F n -> F(n.+1))
                 (k : nat)
        : inc F f k = inc F f k.+1 o f k
        := path_forall _ _ (fun z => (com F f k z)^).

      (* Introduction rule for paths. *)
      Theorem pth_intro (i : sig_path_index Σ) :
        forall (x : colim_path_constr_seq i), endpoint_lhs i x = endpoint_rhs i x.
      Proof.
        simple refine (colim_N_ind _ _ _ _ _).
        - simpl ; intros n x.
          apply (ap (inc _ _ (n.+1)) (path_constr _ i x)).
        - simpl ; intros n x.
          rewrite transport_paths_FlFr.
          rewrite !(colim_N_rec_beta_com _ _ (path_constr_seq_map i)).
          rewrite inv_pp.
          rewrite concat_p_pp.
          rewrite (concat_pp_p _ _ (ap (inc seq constr_seq_map n.+2) (endpointr_coh n i x))).
          rewrite <- (ap_pp (inc seq constr_seq_map n.+2)).
          rewrite ?concat_pp_p.
          rewrite (concat_p_pp (ap (inc seq constr_seq_map n.+2) (endpointl_coh n i x))^).
          rewrite <- ap_V.
          rewrite <- (ap_pp (inc seq constr_seq_map n.+2)).
          rewrite <- (ap_inc seq constr_seq_map n).
          rewrite concat_pp_p.
          f_ap ; f_ap.
          rewrite strong_com.
          refine (ap_compose _ _ _ @ _).
          refine (ap _ _ @ (ap_compose _ _ _)^).
          apply pth_coh.
      Defined.
    End pth_intro.
  End approximating_sequence.

  Arguments constrH {_} {_}.
  Arguments path {_} {_}.
  Arguments sd_i {_} {_}.
  
  (* An approximating sequence is thus a constructing sequence satisfying several invariants.
     These invariants are coherencies and thus, beside adding constructors, we need to add coherencies during the construction.
     This leads to the notion of `coherent_step_data`: this is `step_data` with some extra coherencies.
     From `coherent_step_data` we get all the required rules.
  *)
  Section coherent_step_data.
    (* Here we give the required coherencies for `coherent_step_data`.
       These are mostly similar to the invariants except for the fact they are translated to requirements on `step_data`.
       Only the point coherency is slightly changed, but we can deduce the actual desired coherency from it.
    *)
    Section coherencies.
      Variable (S P Q R : Type)
               (HSP : step_data S P) (HPQ : step_data P Q) (HQR : step_data Q R).

      (* Coherency for the points *)
      Section point_coherency.
        Variable (x : Hcon (r.+1) R).
        
        Definition coh_pt_l := constrH HPQ (Hcon_map (r.+1) ((constrH HQR) o inl) x).
        Definition coh_pt_r := constrH HPQ (Hcon_inA (constrH HQR x)).
      End point_coherency.

      (* Since we need this coherency for the others, we put it in a type class. *)
      Class sd_pt_coh :=
        coh_pt : forall (x : Hcon (r.+1) R), coh_pt_l x = coh_pt_r x.

      (* Coherency for the endpoints*)
      Section endpoint_coherency.
        Variable (i : sig_path_index Σ)
                 (x : poly_act (sig_path_param Σ i) R).
        Context `{sd_pt_coh}.
        
        Definition sd_endpointl
          : sd_i
              HPQ
              (interpret_endpoint_all
                 (sig_path_lhs Σ i)
                 (fst H i)
                 (constrH HQR)
                 x)
            =
            interpret_endpoint_all
              (sig_path_lhs Σ i)
              (fst H i)
              (constrH HPQ)
              (poly_map (sig_path_param Σ i) (sd_i HQR) x).
        Proof.
          rewrite interpret_all_natural.
          - reflexivity.
          - refine (fun p => ap _ (coh_pt _)^).
        Defined.
        
        Definition sd_endpointr
          : sd_i
              HPQ
              (interpret_endpoint_all
                 (sig_path_rhs Σ i)
                 (snd H i)
                 (constrH HQR)
                 x)
            =
            interpret_endpoint_all
              (sig_path_rhs Σ i)
              (snd H i)
              (constrH HPQ)
              (poly_map (sig_path_param Σ i) (sd_i HQR) x).
        Proof.
          rewrite interpret_all_natural.
          - reflexivity.
          - intros.              
            refine (ap _ (coh_pt _)^).
        Defined.
      End endpoint_coherency.

      (* Coherency for the paths. *)
      Section path_coherency.
        Variable (i : sig_path_index Σ)
                 (x : poly_act (sig_path_param Σ i) R).
        Context `{sd_pt_coh}.

        Definition coh_pth_l
          := ap (sd_i HSP)
                ((sd_endpointl i x)
                   @ (path HPQ i (poly_map (sig_path_param Σ i) (sd_i HQR) x))
                   @ (sd_endpointr i x)^).
        
        Definition coh_pth_r
          := ap (sd_i HSP) (ap (sd_i HPQ) (path HQR i x)).
      End path_coherency.
    End coherencies.

    Arguments sd_pt_coh {_} {_} {_} _ _.
    Arguments coh_pth_l {_} {_} {_} {_} _ _ _ _ _.
    Arguments coh_pth_r {_} {_} {_} {_} _ _ _ _.

    (* We have `S` `P`, `Q` and `R` such that we can interpret constructors in `S`, `P`, and `Q` with arguments from `P`, `Q`, and `R` respectively.
       Or, more briefly, we have `step_data S P`, `step_data P Q`, and `step_data Q R`.
       We also need `sd_pt_coh HPQ HQR` to formulate the path coherency.
     *)
    Class coherent_step_data
          {S P Q R : Type}
          (HSP : step_data S P)
          (HPQ : step_data P Q)
          (HQR : step_data Q R)
          {coh_pt : sd_pt_coh HPQ HQR}
      := coh_pth :
           forall (i : sig_path_index Σ)
                  (x : poly_act (sig_path_param Σ i) R),
             coh_pth_l HSP HPQ HQR i x coh_pt
             =
             coh_pth_r HSP HPQ HQR i x.

    Variable (S P Q R : Type)
             (HSP : step_data S P)
             (HPQ : step_data P Q)
             (HQR : step_data Q R)
             (coh_pt : sd_pt_coh HPQ HQR).

    (* The coherency needed for the point introduction rule.
       The point coherency in `coherent_step_data` was changed a bit, but it is still strong enough to acquire the right coherency rule.
    *)
    Lemma point_coherency (C : coherent_step_data HSP HPQ HQR)
          (i : sig_point_index Σ) (x : poly_act (sig_point Σ i) R)
      : (constrH HPQ)
          (Hcon_constr i (poly_map (sig_point Σ i) ((constrH HQR) o inl) x))
        =
        (constrH HPQ)
          (inl ((constrH HQR) (Hcon_constr i x))).
    Proof.
      unfold sd_pt_coh, coh_pt_l, coh_pt_r in coh_pt.
      rewrite <- coh_pt.
      simpl.
      unfold Hcon_constr.
      repeat f_ap.
      apply poly_map_Hcon_inA.
    Defined.
  End coherent_step_data.

  Arguments sd_endpointl {_} {_} {_} _ _ _ _ _.
  Arguments sd_endpointr {_} {_} {_} _ _ _ _ _.
  Arguments sd_pt_coh {_} {_} {_} _ _.
  Arguments coh_pt_l {_} {_} {_}.
  Arguments coh_pt_r {_} {_} {_}.
  Arguments coh_pth_l {_} {_} {_} _ _ _ _ _.
  Arguments coh_pth_r {_} {_} {_} _ _ _ _.
  Arguments coh_pth {_} {_} {_} {_} {_} {_} {_} _ _.
  Arguments point_coherency {_} {_} {_} {_}.

  (* Now we got `coherent_step_data`, which contains the data needed to prove the invariants.
     A `construction_sequence` is a sequence such that at each level we have `step_data`.
     A `coherent_construction_sequence` is a sequence such that at each level we have `coherent_step_data`.
  *)
  Section coherent_construction_sequence.
    Class coh_constr_seq
          (F : nat -> Type)
          `{constr_seq F}
          `{forall n, sd_pt_coh (constr n.+1) (constr n)}
      := coh_constr : forall (n : nat),
          coherent_step_data (constr n.+2) (constr n.+1) (constr n).

    (* We work with an arbitrary coherent construction sequence. *)
    Variable (seq : nat -> Type).
    Context `{constr_seq seq}
            `{forall n, sd_pt_coh (constr n.+1) (constr n)}.
    Variable (coh_seq : coh_constr_seq seq).

    (* The invariant for the introduction rule for the points is satisfied. *)
    Global Instance point_intro_coherent_coh : point_intro_coherent seq.
    Proof.
      intros n.
      refine (point_coherency _ _ _ _ _).
      apply coh_seq.
    Defined.

    (* The invariant for interpreting the endpoints is satisfied. *)
    Global Instance endpoint_coherent_coh : endpoint_coherent seq.
    Proof.
      split.
      - intros.
        refine (sd_endpointl _ _ _ _ _)^.
      - intros.
        refine (sd_endpointr _ _ _ _ _)^.
    Defined.

    (* The invariant the introduction rule for the paths is satisfied. *)
    Global Instance path_intro_coherent_coh : path_intro_coherent seq.
    Proof.
      intros n i x.
      pose (@coh_pth _ _ _ _ _ _ _ _ (coh_seq n) i x) as p.
      unfold coh_pth_l, coh_pth_r in p.
      unfold path_coherent_left, path_coherent_right.
      simpl.
      rewrite <- p.
      hott_simpl.
    Defined.
  End coherent_construction_sequence.
  
  (* Hence, a `coherent_construction_sequence` satisfies all invariants, so we get the introduction rules for it.
     For an approximating sequence, it suffices to build a coherent construction sequence.
     That is done by adding a data in a coherent way.
     First, we add step data.
     Then using coequalizers and path coequalizers we get the coherencies.
     This gives coherent step data.
     The approximator does all these steps.
  *)
  Section approximator.
    (* First, we add `step_data`.
       This requires one argument.
       To acquire the point constructors, we use `Hcon`.
       To acquire the path constructors, we use a coequalizer.
       This way we get a type with `step_data` over `P`.
    *)
    Section add_constructors.
      Variable (P : Type).
               
      Definition params : Type
        := {i : sig_path_index Σ & poly_act (sig_path_param Σ i) P}.

      Definition path_1 (y : params) : Hcon (r.+1) P
        := interpret_endpoint (sig_path_lhs Σ y.1) (fst H y.1) y.2.

      Definition path_2 (y : params) : Hcon (r.+1) P
        := interpret_endpoint (sig_path_rhs Σ y.1) (snd H y.1) y.2.

      Definition add_cons : Type :=
        Coeq path_1 path_2.

      Global Instance H_add_cons_P : step_data add_cons P
        := {|constrH := coeq ; path := fun i x => cp (i;x)|}.
    End add_constructors.

    (* Furthermore, we can add `step_data` together with the point coherency.
       This requires two arguments.
       We first use the previous construction to add `step_data` and then we obtain the coherency with a coequalizer.
    *)
    Section add_point_coherency.
      Variable (P Q : Type)
               (HPQ : step_data P Q).
      
      Definition add_pt_coherency : Type
        := Coeq (coh_pt_l (H_add_cons_P P) HPQ) (coh_pt_r (H_add_cons_P P) HPQ).

      (* We still have `step_data`. *)
      Global Instance H_pt_coh_P : step_data add_pt_coherency P.
      Proof.
        simple refine {|constrH := coeq o (constrH _) ; path := _|}.
        intros.
        refine (ap coeq (cp (i;x))).
      Defined.

      Global Instance pt_coh_PQR : sd_pt_coh H_pt_coh_P HPQ
        := fun x => cp x.
    End add_point_coherency.

    (* Lastly, we can add `step_data`, the point coherency and the path coherency.
       This requires three arguments.
       The path coherency is added with a path coequalizer.
       This gives `coherent_step_data`.
    *)
    Section add_path_coherency.
      Variable (P Q R : Type)
               (HPQ : step_data P Q)
               (HQR : step_data Q R).
      Context `{@sd_pt_coh _ _ _ HPQ HQR}.

      (* Next we add coherencies for the paths *)
      Definition path_coherencies :
        {i : sig_path_index Σ & poly_act (sig_path_param Σ i) R}
        ->
        {b1 : add_pt_coherency P Q HPQ &
              {b2 : add_pt_coherency P Q HPQ & (b1 = b2) * (b1 = b2)}}.
      Proof.
        intros [i x].
        refine (_;(_;(_,_))).
        - simple refine (coh_pth_l _ _ HPQ HQR i x _).
        - refine (coh_pth_r _ _ _ _ i x).
      Defined.

      (* This type has all the coherencies. *)
      Definition add_pth_coherencies : Type
        := pcoeq path_coherencies.

      (* We have step data. *)
      Global Instance H_pth_coherencies_P : step_data add_pth_coherencies P.
      Proof.
        simple refine {|constrH := inP _ o (constrH _) ; path := _|}.
        intros i x.
        refine (ap (inP _) (path _ i x)).
      Defined.

      (* We have the point coherency. *)
      Global Instance pt_coh_SPQ : sd_pt_coh H_pth_coherencies_P HPQ
        := fun x => ap (inP _) (cp _).

      (* We have coherent step data. *)
      Global Instance coherent_step_data_PSQR
        : coherent_step_data H_pth_coherencies_P HPQ HQR.
      Proof.
        intros i x.
        unfold coh_pth_l, coh_pth_r, sd_i, constrH.
        simpl.
        refine (ap_compose _ _ _ @ _).
        refine (glueP path_coherencies (i;x) @ _).
        refine (ap_compose _ _ _)^.
      Defined.
    End add_path_coherency.
  End approximator.

  (* From the approximator, we can build a `coherent_construction_sequence`. *)
  Section coherent_construction_sequence_existence.
    (* Let's start with the base cases. *)
    Definition seq_z : Type := Empty.
    Definition seq_o : Type := add_cons seq_z.
    Definition seq_t : Type := add_pt_coherency seq_o seq_z _.

    (* We want to build the sequence inductively, but that gives a problem.
       If we want to use the approximator, we need structure relating `F(n+2)`, `F(n+1)`, and `F(n)` and this structure, is not present automatically.
       To solve this, we first build a sequence sending `n` to `(F n;F(n+1);F(n+2);_;_;_)`.
       The last three coordinates give `step_data F(n+2) F(n+1)`, `step_data F(n+1) (F n)` and the point coherency respectively.
       This allows us to use the approximator and then we can build the sequence.
    *)
    Definition help_seq (n : nat)
      : {R : Type &
             {Q : Type &
                  {P : Type &
                       {HPQ : step_data P Q &
                              {HQR : step_data Q R & sd_pt_coh HPQ HQR}}}}}.
    Proof.
      induction n as [ | n IHn].
      - refine (seq_z;(seq_o;(seq_t;(_;(_;_))))).
        apply _.
      - destruct IHn as [R [Q [P [HPQ [HQR Hcoh]]]]].
        refine (Q;(P;((add_pth_coherencies _ _ _ _ _);(_;(_;_))))).
        apply _.
    Defined.

    (* The desired sequence is the the first coordinate of the help sequence. *)
    Definition seq (n : nat) := (help_seq n).1.

    (* We show it is indeed a `coherent_constructor_sequence`. *)
    Global Instance seq_is_constr_seq : constr_seq seq
      := fun n => (help_seq n).2.2.2.2.1.

    Definition seq_point_coh : forall n, sd_pt_coh (constr n.+1) (constr n)
      := fun n => (help_seq n).2.2.2.2.2.

    Global Instance seq_is_coh_cosntr_seq : @coh_constr_seq seq _ seq_point_coh
      := fun _ => _.
  End coherent_construction_sequence_existence.    
End hit_existence.