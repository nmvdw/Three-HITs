(* We formulate the main theorem, which states that all HITs exist, provided that several
   kinds of HITs do. *)

Require Import HoTT.
Require Import polynomial.
Require Import hit_structure.
Require Import HoTT.HIT.Colimits.
Require Import colim.

Section hit_existence.
  Variable (Σ : hit_signature).

  (* In order to build the approximating sequence, we first need to be able to construct types in which the constructor terms can be interpreted.
     We first define a type `Hcon A n` in which endpoints of depth `n` and parameters in `A` can be interpreted.
     In addition we show that whenever we have a map `Hcon A n -> B`, then we can interpret endpoints of depth `n` with parameters in `A` in `B` as well.    
  *)
  Section add_constructors.
    (* Given a functor `F`, then `Hcon n A = A + F A + ... + Fⁿ A`.
       In this case, `F X = {i : sig_point_index Σ & poly_act (sig_point Σ i) (Hcon n A)}`
     *)
    Fixpoint Hcon (n : nat) (A : Type) : Type :=
      match n with
      | 0 => A
      | S n => A + {i : sig_point_index Σ & poly_act (sig_point Σ i) (Hcon n A)}
      end.

    (* `Hcon n` is a functor *)
    Fixpoint Hcon_map {A B : Type} (n : nat) (f : A -> B)
      : Hcon n A -> Hcon n B
      := match n with
         | 0 => f
         | S n =>
           fun x =>
             match x with
             | inl x => inl(f x)
             | inr (i;x) => inr(i;poly_map _ (Hcon_map n f) x)
             end
         end.

    (* Inclusions of `A` into `Hcon n` *)
    Definition Hcon_inA {A : Type} {n : nat} (x : A) : Hcon n A :=
      match n with
      | 0 => idmap x
      | S n => inl x
      end.

    (* Coherency relating `Hcon_inA` and `Hcon_map` *)
    Definition coherency_map_in {Q R : Type} n (f : Hcon (n.+1) R -> Q) x :
      Hcon_inA (f (inl x)) = Hcon_map n (fun x0 : R => f (inl x0)) (Hcon_inA x).
    Proof.
      induction n ; reflexivity.
    Defined.

    (* Intepret constructors in `Hcon (n.+1)` with arguments from `A` *)
    Definition Hcon_constr {A : Type} {n : nat}
               (i : sig_point_index Σ) (x : poly_act (sig_point Σ i) A)
      : Hcon (n.+1) A
      := inr(i;poly_map _ Hcon_inA x).

    (* Intepret constructors in `Hcon (n.+1)` with arguments from `Hcon n A` *)
    Definition Hcon_C {A : Type} {n : nat}
               {i : sig_point_index Σ} (x : poly_act (sig_point Σ i) (Hcon n A))
      : Hcon (n.+1) A
      := inr(i;x).

    (* Endpoints of rank `n` can be interpreted in `Hcon A` *)
    Fixpoint interpret_endpoint {A : Type} {P Q : polynomial} {n : nat}
             (e : endpoint (sig_point Σ) P Q)
             (H : endpoint_rank (sig_point Σ) e n)
      : poly_act P A -> poly_act Q (Hcon n A)
      := match H with
         | rank_var _ _ => poly_map _ Hcon_inA
         | rank_const _ _ t _ => fun _ => t
         | rank_constr _ _ _ e H => fun x => Hcon_C (interpret_endpoint e H x)
         | rank_fst _ _ _ _ e H => fun x => fst(interpret_endpoint e H x)
         | rank_snd _ _ _ _ e H => fun x => snd(interpret_endpoint e H x)
         | rank_inl _ _ _ _ e H => fun x => inl(interpret_endpoint e H x)
         | rank_inr _ _ _ _ e H => fun x => inr(interpret_endpoint e H x)
         end.

    (* Endpoints of rank `n` can be interpreted in `B` given `Hcon A -> B` *)
    Definition interpret_endpoint_all {A B : Type} {P Q : polynomial} {n : nat}
               (e : endpoint (sig_point Σ) P Q)
               (H : endpoint_rank (sig_point Σ) e n)
               (f : Hcon n A -> B) (x : poly_act P A)
      : poly_act Q B
      := poly_map Q f (interpret_endpoint e H x).

    (* Interpreting endpoints is a natural transformation. *)
    Definition interpret_natural
               {A B : Type}
               {P Q : polynomial}
               {n : nat}
               (e : endpoint (sig_point Σ) P Q)
               (H : endpoint_rank (sig_point Σ) e n)
               (f : A -> B)
               (x : poly_act P A)
      : interpret_endpoint e H ((poly_map P f) x)
        =
        poly_map Q (Hcon_map n f) (interpret_endpoint e H x).
    Proof.
      induction H as
          [ | | ? ? ? ? ? IHe | ? ? ? ? ? ? IHe | ? ? ? ? ? ? IHe
            | ? ? ? ? ? ? IHe | ? ? ? ? ? ? IHe]; simpl.
      - induction P  as [ | | ? IHP1 ? IHP2 | ? IHP1 ? IHP2 ] ; simpl.
        * destruct n ; reflexivity.            
        * reflexivity.
        * refine (path_prod' (IHP1 (fst x)) (IHP2 (snd x))).
        * destruct x as [z1 | z2].
          ** refine (ap inl (IHP1 z1)).
          ** refine (ap inr (IHP2 z2)).  
      - reflexivity.
      - refine (ap Hcon_C (IHe x)).
      - refine (ap fst (IHe x)).
      - refine (ap snd (IHe x)).
      - refine (ap inl (IHe x)).
      - refine (ap inr (IHe x)).
    Defined.

    (* Given an extra coherency, `interpret_endpoint_all` commutes with maps `g : Hcon n B -> C` *)
    Definition interpret_all_natural
               {A B C D : Type}
               {P : polynomial}
               {n : nat}
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
        h (interpret_endpoint_all e H g (poly_map P (f o Hcon_inA) x)).
    Proof.
      unfold interpret_endpoint_all.
      rewrite interpret_natural.
      apply coh.
    Defined.
        
  End add_constructors.

  (*
    HITs are constructed as a colimit of a sequence of type.
    This sequence satisfies some invariants, namely that at every step a certain amount of paths and constructors is added.
    This is encapsulated in `step_data`.
    In this `step_data` data for the introduction rules, elimination rule, and computation rule is contained.
    We require the rank of the HIT to be atleast 1.
  *)
  Section step_data.
    Variable (n : nat) (H : hit_rank Σ (S n)).

    (* In `P` we can interpret the point and path constructors with arguments from `Q`. *)
    Structure step_data (P Q : Type) :=
      {
        constrH : Hcon (n.+1) Q -> P ;
        path : forall (i : sig_path_index Σ) (x : poly_act (sig_path_param Σ i) Q),
            interpret_endpoint_all (sig_path_lhs Σ i) (fst H i) constrH x
            =
            interpret_endpoint_all (sig_path_rhs Σ i) (snd H i) constrH x ;
      }.

    Arguments constrH {_} {_} _ _.
    Arguments path {_} {_} _ _ _.

    (* We have `P`, `Q` and `R` such that we can interpret constructors in `P` and `Q` with arguments from `Q` and `R` respectively.
       Also, a coherency condition is required to relate the step data.
     *)
    Structure coherent_step_data (P Q R : Type) :=
      {
        HPQ : @step_data P Q ;
        HQR : @step_data Q R ;
        coh_pt : forall (x : Hcon (n.+1) R),
            (constrH HPQ) (Hcon_map (n.+1) ((constrH HQR) o inl) x)
            =
            (constrH HPQ) (Hcon_inA (constrH HQR x))
      }.

    Arguments HPQ {_} {_} {_} _.
    Arguments HQR {_} {_} {_} _.
    Arguments coh_pt {_} {_} {_} _ _.

    (* Inclusions *)
    Definition sd_i {P Q : Type} (Hstep : step_data P Q) (x : Q) : P
      := (constrH Hstep) (Hcon_inA x).

    (* The coherency needed for the point introduction rule *)
    Lemma point_coherency P Q R (C : @coherent_step_data P Q R)
          (i : sig_point_index Σ) (x : poly_act (sig_point Σ i) R)
      : (constrH (HPQ C)) (Hcon_constr i (poly_map (sig_point Σ i) ((constrH (HQR C)) o inl) x))
        =
        (constrH (HPQ C)) (inl ((constrH (HQR C)) (Hcon_constr i x))).
    Proof.
      rewrite <- coh_pt.
      simpl.
      unfold Hcon_constr.
      repeat f_ap.
      induction (sig_point Σ i) ; simpl.
      - apply coherency_map_in.
      - reflexivity.
      - rewrite IHp1, IHp2 ; reflexivity.
      - destruct x ; rewrite IHp1 || rewrite IHp2 ; reflexivity.
    Defined.

    (*
      From `coherent_step_data` we can make a cone for the point introduction rule.
     *)
    Section point_cone.
      Variable (i : sig_point_index Σ).
      
      Definition sd_p_c {P Q : Type} (Hstep : @step_data P Q)
                 (x : poly_act (sig_point Σ i) Q) : P
        := (constrH Hstep) (Hcon_constr i x).           

      Definition sd_p_cone
                 {P Q R : Type}
                 (Hstep : @coherent_step_data P Q R)
                 (x : poly_act (sig_point Σ i) R)
        : sd_p_c (HPQ Hstep) (poly_map (sig_point Σ i) (sd_i (HQR Hstep)) x)
          =
          sd_i (HPQ Hstep) (sd_p_c (HQR Hstep) x).
      Proof.
        apply point_coherency.
      Defined.      
    End point_cone.

    (*
      From `coherent_step_data` we can make a cone for the path introduction rule.
    *)
    Section path_cone.
      Definition sd_pt_c (i : sig_path_index Σ) {P Q : Type} (Hstep : @step_data P Q)
                 (x : poly_act (sig_path_param Σ i) Q)
      : interpret_endpoint_all (sig_path_lhs Σ i) ((fst H) i) (constrH Hstep) x
        =
        interpret_endpoint_all (sig_path_rhs Σ i) ((snd H) i) (constrH Hstep) x
        := path Hstep i x.
    End path_cone.
                                  
  End step_data.

    Arguments constrH {_} {_} {_} {_} _ _.
    Arguments path {_} {_} {_} {_} _ _ _.
    Arguments HPQ {_} {_} {_} {_} {_} _.
    Arguments HQR {_} {_} {_} {_} {_} _.
    Arguments coh_pt {_} {_} {_} {_} {_} _ _.

  (*
    In order to build the approximating sequence, we need to be able to build add coherent step data.
    For that we first show how to add step data.
    This is done with a coequalizer.
    Secondly, we show how to make coherent step data.
  *)
  Section approximating_sequence.
    Variable (n : nat) (H : hit_rank Σ (S n)).

    Definition params (Q : Type) : Type
      := {i : sig_path_index Σ & poly_act (sig_path_param Σ i) Q}.

    Definition path_1 (Q : Type) (y : params Q) : Hcon (n.+1) Q
      := interpret_endpoint (sig_path_lhs Σ y.1) (fst H y.1) y.2.

    Definition path_2 (Q : Type) (y : params Q) : Hcon (n.+1) Q
      := interpret_endpoint (sig_path_rhs Σ y.1) (snd H y.1) y.2.

    (* Add paths to Hcon *)
    Definition ap_Hcon (Q : Type) : Type :=
      Coeq (path_1 Q) (path_2 Q).
        
    Definition add_step (Q : Type) : {P : Type & step_data n H P Q}
      := (ap_Hcon Q;{|constrH := coeq ; path := fun i x => cp (i;x)|}).

    Definition coh_param (R Q : Type) : Type
      := Hcon (n.+1) R.
    
    Definition coh_l {R Q : Type} (jR : Hcon (n.+1) R -> Q) (z : coh_param R Q)
      : Hcon (n.+1) Q
      := Hcon_map (n.+1) (jR o inl) z.

    Definition coh_r {R Q : Type} (jR : Hcon (n.+1) R -> Q) (z : coh_param R Q)
      : Hcon (n.+1) Q
      := inl (jR z).

    (* Adds coherencies ass well *)
    Definition apc_Hcon (Q R : Type) (Hstep : step_data n H Q R) : Type
      :=
        @Coeq (coh_param R Q) (ap_Hcon Q)
              (coeq o (coh_l (constrH Hstep)))
              (coeq o (coh_r (constrH Hstep))).

    Definition add_cstep (R Q : Type) (Hstep : step_data n H Q R)
      : {P : Type & @coherent_step_data n H P Q R}.
    Proof.
      exists (apc_Hcon Q R Hstep).
      simple refine {|HPQ := _ ; HQR := Hstep ; coh_pt := _|}.
      - refine {|constrH := coeq o coeq ; path := _|}.
        intros.
        refine (ap coeq _).
        apply (@cp _ _ (path_1 Q) (path_2 Q) (i;x)).
      - intros x.
        simple refine (@cp _ _ _ _ _).
    Defined.

    Definition approximating_sequence :=
      {seq : nat -> Type & forall m, @coherent_step_data n H (seq (S(S m))) (seq (S m)) (seq m)}.

    Definition approx_map (seq : approximating_sequence) (k : nat) : seq.1 k -> seq.1 (S k) :=
      match seq with
      | (seq;Hseq) => (constrH (HQR (Hseq k))) o Hcon_inA
      end.

    Definition approx_colimit (seq : approximating_sequence) :=
      colim_N (seq.1) (approx_map seq).
    
  End approximating_sequence.

  Section approximating_sequence_existence.
    Variable (n : nat) (H : hit_rank Σ (S n)).
    
    Theorem sequence_existence : approximating_sequence n H.
    Admitted.

  End approximating_sequence_existence.

  Section approximating_sequence_colimit.
    Variable (n : nat) (H : hit_rank Σ (S n)) (Happrox : approximating_sequence n H).

    Theorem hit_existence : HIT Σ.
    Proof.
    Admitted.

  End approximating_sequence_colimit.
End hit_existence.
