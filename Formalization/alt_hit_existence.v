(* We formulate the main theorem, which states that all HITs exist, provided that several
   kinds of HITs do. *)

Require Import HoTT.
Require Import polynomial.
Require Import hit_structure.
Require Import HoTT.HIT.Colimits.
Require Import colim.
Require Import pcoeq.

Section hit_existence.
  Variable (Σ : hit_signature).

  (* In order to build the approximating sequence, we first need to be able to construct types in which the constructor terms can be interpreted.
     We first define a type `Hcon A n` in which endpoints of depth `n` and parameters in `A` can be interpreted.
     In addition we show that whenever we have a map `Hcon A n -> B`, then we can interpret endpoints of depth `n` with parameters in `A` in `B` as well.    
  *)
  Section add_constructors.
    (* Define `F X = {i : sig_point_index Σ & poly_act (sig_point Σ i) (Hcon n A)}`.
       Then `Hcon n A = A + F A + ... + Fⁿ A`.
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

    Definition Hcon_map_id {A : Type} (n : nat) (x : Hcon n A)
      : Hcon_map n (idmap) x = x.
    Proof.
      induction n as [ | n IHn] ; simpl.
      - reflexivity.
      - destruct x as [ | [i z]].
        * reflexivity.
        * refine (ap (fun a => inr(i;a)) _).
          induction (sig_point Σ i) ; simpl.
          ** apply IHn.
          ** reflexivity.
          ** refine (path_prod' (IHp1 _) (IHp2 _)).
          ** destruct z.
             *** apply (ap inl (IHp1 _)).
             *** apply (ap inr (IHp2 _)).
    Defined.

    Definition Hcon_map_compose {A B C : Type} (n : nat) (f : A -> B) (g : B -> C) :
      forall (x : Hcon n A), Hcon_map n (g o f) x = Hcon_map n g (Hcon_map n f x).
    Proof.
      intro x.
      induction n as [ | n IHn] ; simpl.
      - reflexivity.
      - destruct x as [ | [i z]].
        * reflexivity.
        * refine (ap (fun a => inr(i;a)) _).
          induction (sig_point Σ i).
          ** apply IHn.
          ** reflexivity.
          ** refine (path_prod' (IHp1 _) (IHp2 _)).
          ** destruct z.
             *** apply (ap inl (IHp1 _)).
             *** apply (ap inr (IHp2 _)).
    Defined.

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

    (* Inclusions *)
    Definition sd_i {P Q : Type} (Hstep : step_data P Q) (x : Q) : P
      := (constrH Hstep) (Hcon_inA x).

    (* In this section we give the required coherencies *)
    Section coherencies.
      Variable (P Q R : Type)
               (HPQ : step_data P Q)
               (HQR : step_data Q R).

      (* Coherency for the points *)
      Definition coh_pt_l (x : Hcon (n.+1) R) :=
        (constrH HPQ) (Hcon_map (n.+1) ((constrH HQR) o inl) x).

      Definition coh_pt_r (x : Hcon (n.+1) R) :=
        (constrH HPQ) (Hcon_inA (constrH HQR x)).

      Variable (i : sig_path_index Σ)
               (coh_pt : forall (x : Hcon (n.+1) R),
                   coh_pt_l x = coh_pt_r x).      
      
      Definition q1 (x : poly_act (sig_path_param Σ i) R)
        :
          interpret_endpoint_all (sig_path_lhs Σ i) (fst H i) (constrH HPQ)
                                 (poly_map (sig_path_param Σ i) (sd_i HQR) x)
          =
          sd_i HPQ
               (interpret_endpoint_all (sig_path_lhs Σ i) (fst H i) (constrH HQR) x).
      Proof.
        rewrite interpret_all_natural.
        - unfold sd_i.
          reflexivity.
        - intro p.
          refine (ap _ (coh_pt _)^).
      Defined.
      
      Definition q2 (x : poly_act (sig_path_param Σ i) R)
        :
          sd_i HPQ
               (interpret_endpoint_all (sig_path_rhs Σ i) (snd H i) (constrH HQR) x)
          =
          interpret_endpoint_all (sig_path_rhs Σ i) (snd H i) (constrH HPQ)
                                 (poly_map (sig_path_param Σ i) (sd_i HQR) x).
      Proof.
        rewrite interpret_all_natural.
        - unfold sd_i.
          reflexivity.
        - intro p.              
          refine (ap _ (coh_pt _)^).
      Defined.

      Definition coh_pth_l (x : poly_act (sig_path_param Σ i) R)
        := q1 x @ ap (sd_i HPQ) (path HQR i x) @ q2 x.

      Definition coh_pth_r (x : poly_act (sig_path_param Σ i) R)
        := path HPQ i (poly_map (sig_path_param Σ i) (sd_i HQR) x).
    End coherencies.

    Arguments q1 {_} {_} {_} _ _ _ _ _.
    Arguments q2 {_} {_} {_} _ _ _ _ _.
    Arguments coh_pt_l {_} {_} {_}.
    Arguments coh_pt_r {_} {_} {_}.
    Arguments coh_pth_l {_} {_} {_} _ _ _ _ _.
    Arguments coh_pth_r {_} {_} {_} _ _ _ _.

    (* We have `P`, `Q` and `R` such that we can interpret constructors in `P` and `Q` with arguments from `Q` and `R` respectively.
       Also, a coherency condition is required to relate the step data.
     *)
    Structure coherent_step_data (S P Q R : Type) :=
      {
        HSP : step_data S P ;
        HPQ : step_data P Q ;
        HQR : step_data Q R ;
        coh_pt_PQ : forall (x : Hcon (n.+1) R),
            coh_pt_l HPQ HQR x = coh_pt_r HPQ HQR x ;
        coh_pt_SP : forall (x : Hcon (n.+1) Q),
            coh_pt_l HSP HPQ x = coh_pt_r HSP HPQ x ;
        coh_pth : forall (i : sig_path_index Σ) (x : poly_act (sig_path_param Σ i) R),
            ap (sd_i HSP) (coh_pth_l HPQ HQR i coh_pt_PQ x)
            =
            ap (sd_i HSP) (coh_pth_r HPQ HQR i x)
      }.

    Arguments HSP {_} {_} {_} {_} _.
    Arguments HPQ {_} {_} {_} {_} _.
    Arguments HQR {_} {_} {_} {_} _.
    Arguments coh_pt_PQ {_} {_} {_} {_} _ _.
    Arguments coh_pt_SP {_} {_} {_} {_} _ _.
    Arguments coh_pth {_} {_} {_} {_} _ _ _.

    (* The coherency needed for the point introduction rule *)
    Lemma point_coherency S P Q R (C : coherent_step_data S P Q R)
          (i : sig_point_index Σ) (x : poly_act (sig_point Σ i) R)
      : (constrH (HPQ C)) (Hcon_constr i (poly_map (sig_point Σ i) ((constrH (HQR C)) o inl) x))
        =
        (constrH (HPQ C)) (inl ((constrH (HQR C)) (Hcon_constr i x))).
    Proof.
      pose (coh_pt_PQ C) as coh_pt'.
      unfold coh_pt_l, coh_pt_r in coh_pt'.
      rewrite <- coh_pt'.
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
      
      Definition sd_p_c {P Q : Type} (Hstep : step_data P Q)
                 (x : poly_act (sig_point Σ i) Q) : P
        := (constrH Hstep) (Hcon_constr i x).           

      Definition sd_p_cone
                 {P Q R S : Type}
                 (Hstep : coherent_step_data S P Q R)
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
      Variable (i : sig_path_index Σ).
      
      Definition sd_pt_c {P Q : Type} (Hstep : step_data P Q)
                 (x : poly_act (sig_path_param Σ i) Q)
      : interpret_endpoint_all (sig_path_lhs Σ i) ((fst H) i) (constrH Hstep) x
        =
        interpret_endpoint_all (sig_path_rhs Σ i) ((snd H) i) (constrH Hstep) x
        := path Hstep i x.
      
      Definition sd_pth_cone {P Q R S : Type}
                 (Hstep : coherent_step_data S P Q R)
                 (x : poly_act (sig_path_param Σ i) R) 
        : ap (sd_i (HSP Hstep))
             (q1 (HPQ Hstep) (HQR Hstep) i (coh_pt_PQ Hstep) x
             @ ap (sd_i (HPQ Hstep)) (sd_pt_c (HQR Hstep) x)
             @ q2 (HPQ Hstep) (HQR Hstep) i (coh_pt_PQ Hstep) x)
          =
          ap
            (sd_i (HSP Hstep))
            (sd_pt_c (HPQ Hstep) (poly_map (sig_path_param Σ i) (sd_i (HQR Hstep)) x)).
      Proof.
        apply coh_pth.
      Defined.
            
    End path_cone.
                                  
  End step_data.

  Arguments constrH {_} {_} {_} {_} _ _.
  Arguments path {_} {_} {_} {_} _ _ _.
  Arguments HPQ {_} {_} {_} {_} {_} {_} _.
  Arguments HQR {_} {_} {_} {_} {_} {_} _.
  Arguments coh_pt_PQ {_} {_} {_} {_} {_} _ _.
  Arguments coh_pt_SP {_} {_} {_} {_} {_} _ _.
  Arguments q1 {_} {_} {_} _ _ _ _ _.
  Arguments q2 {_} {_} {_} _ _ _ _ _.
  Arguments coh_pt_l _ _ {_} {_} {_}.
  Arguments coh_pt_r _ _ {_} {_} {_}.
  Arguments coh_pth_l _ _ {_} {_} {_} _ _ _ _ _.
  Arguments coh_pth_r _ _ {_} {_} {_} _ _ _ _.

  (*
    In order to build the approximating sequence, we need to be able to build add coherent step data.
    For that we first show how to add step data.
    This is done with a coequalizer.
    Secondly, we show how to make coherent step data.
  *)
  Section approximator.
    Variable (n : nat) (H : hit_rank Σ (S n))
             (P Q R : Type)
             (HsPQ : step_data n H P Q)
             (HsQR : step_data n H Q R)
             (coh_pt_PQR : forall (x : Hcon (n.+1) R),
            coh_pt_l n H HsPQ HsQR x = coh_pt_r n H HsPQ HsQR x).

    (* First we add the path constructors to `Hcon (n.+1) Q` with a coequalizer. *)
    Definition params : Type
      := {i : sig_path_index Σ & poly_act (sig_path_param Σ i) P}.

    Definition path_1 (y : params) : Hcon (n.+1) P
      := interpret_endpoint (sig_path_lhs Σ y.1) (fst H y.1) y.2.

    Definition path_2 (y : params) : Hcon (n.+1) P
      := interpret_endpoint (sig_path_rhs Σ y.1) (snd H y.1) y.2.

    Definition add_paths : Type :=
      Coeq path_1 path_2.

    (* This gives `step data` *)
    Definition HsSP1 : step_data n H add_paths P
      := {|constrH := coeq ; path := fun i x => cp (i;x)|}.
    
    (* Next we add the coherencies for the points *)
    Definition add_pt_coherencies : Type
      := Coeq (coh_pt_l n H HsSP1 HsPQ) (coh_pt_r n H HsSP1 HsPQ).

    Definition HsSP2 : step_data n H add_pt_coherencies P.
    Proof.      
      simple refine {|constrH := coeq o (constrH HsSP1) ; path := _|}.
      intros.
      refine (ap coeq (@cp _ _ path_1 path_2 (i;x))).
    Defined.    

    (* Next we add coherencies for the paths *)

    Definition path_coherencies : {i : sig_path_index Σ & poly_act (sig_path_param Σ i) R} ->
      {b1 : add_pt_coherencies & {b2 : add_pt_coherencies & (b1 = b2) * (b1 = b2)}}.
    Proof.
      intros [i x].
      refine (_;(_;(_,_))).
      - refine (ap (sd_i n H HsSP2) (coh_pth_l n H HsPQ HsQR i _ x)).
        intros.
        apply coh_pt_PQR.
      - refine (ap (sd_i n H HsSP2) (coh_pth_r n H HsPQ HsQR i x)).
    Defined.

    Definition add_pth_coherencies : Type
      := pcoeq path_coherencies.

    Definition HsSP : step_data n H add_pth_coherencies P.
    Proof.
      simple refine {|constrH := inP _ o (constrH HsSP2) ; path := _|}.
      intros.
      refine (ap (inP _) (path HsSP2 i x)).
    Defined.
    
    Definition coherent_step_data_PSQR : coherent_step_data n H add_pth_coherencies P Q R.
    Proof.
      simple refine {|HSP := HsSP ; HPQ := HsPQ ; HQR := HsQR ; coh_pt_PQ := coh_pt_PQR ;
                      coh_pt_SP := _ ; coh_pth := _|}.
      - intros.
        refine (ap (inP _) _).
        simple refine (@cp _ _ _ _ _).
      - intros.
        unfold sd_i, constrH.
        simpl.
        refine (ap_compose _ _ _ @ _).
        refine (glueP path_coherencies (i;x) @ _).
        refine (_ @ (ap_compose _ _ _)^).
        reflexivity.
    Defined.

  End approximator.

  Section approximating_sequence.
    Variable (n : nat) (H : hit_rank Σ (S n)).

    Definition approximating_sequence :=
      {seq : nat -> Type & forall m,
                 coherent_step_data n H (seq (m.+3)) (seq (m.+2)) (seq (m.+1)) (seq m)}.

    Definition approx_map (seq : approximating_sequence) (k : nat) : seq.1 k -> seq.1 (k.+1)
      := match seq with
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
