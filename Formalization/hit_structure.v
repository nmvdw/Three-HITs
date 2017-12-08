Require Import HoTT.
Require Import polynomial.

Section Endpoints.
  (* The definition of a HIT signature and a HIT for the signature. *)

  (* An endpoint is also called a "constructor term". It is used in
the HIT signature to describe the endpoints of path constructors. *)

  (* Endpoints are parameterized by a family of polynomials which will
be specialized to the point constructors in the definition of HITS.
   *)
  Variable (I : Type)
           (C : I -> polynomial).

  Inductive endpoint : polynomial -> polynomial -> Type :=
  | endpoint_var :
      forall {P : polynomial},
        endpoint P P
  | endpoint_const :
      forall {P : polynomial} {T : Type},
        T -> endpoint P (poly_const T)
  | endpoint_constr :
      forall {P : polynomial} (i : I),
        endpoint P (C i) -> endpoint P poly_var
  | endpoint_fst :
      forall {P Q R : polynomial},
        endpoint P (poly_times Q R) -> endpoint P Q
  | endpoint_snd :
      forall {P Q R : polynomial},
        endpoint P (poly_times Q R) -> endpoint P R
  | endpoint_pair :
      forall {P Q R : polynomial},
        endpoint P Q -> endpoint P R -> endpoint P (poly_times Q R)
  | endpoint_inl :
      forall {P Q R : polynomial},
        endpoint P Q -> endpoint P (poly_plus Q R)
  | endpoint_inr :
      forall {P Q R : polynomial},
        endpoint P R -> endpoint P (poly_plus Q R).

  Variable (A : Type)
           (F : A -> Type)
           (c : forall (i : I), poly_act (C i) A -> A)
           (f : forall (i : I) (u : poly_act (C i) A), poly_fam (C i) F u -> F (c i u)).

  (* Endpoint acting on data for point constructors. *)
  Fixpoint endpoint_act
           {P Q : polynomial}
           (e : endpoint P Q) (* the endpoint *)
    : poly_act P A -> poly_act Q A
    := match e with
       | endpoint_var _ => idmap
       | endpoint_const _ _ t => fun _ => t
       | endpoint_constr _ i e => fun u => c i (endpoint_act e u) 
       | endpoint_fst _ _ _ e => fun u => fst(endpoint_act e u)
       | endpoint_snd _ _ _ e => fun u => snd(endpoint_act e u)
       | endpoint_pair _ _ _ e1 e2 => fun u => (endpoint_act e1 u, endpoint_act e2 u)
       | endpoint_inl _ _ _ e => fun u => inl(endpoint_act e u)
       | endpoint_inr _ _ _ e => fun u => inr(endpoint_act e u)
       end.

  (* The dependent action of an endpoint, this is used for
   "lifting" the path constructors in the elimination principle. *)
  Fixpoint endpoint_dact
           {P Q : polynomial}
           (e : endpoint P Q)
    : forall (x : poly_act P A), poly_fam P F x -> poly_fam Q F (endpoint_act e x)
    := match e with
       | endpoint_var _ => fun _ h => h
       | endpoint_const _ _ t => fun _ _ => t
       | endpoint_constr _ i u => fun x h =>f i (endpoint_act u x) (endpoint_dact u x h)
       | endpoint_fst p p0 p1 e => fun x h => fst (@endpoint_dact p (poly_times p0 p1) e x h)
       | endpoint_snd p p0 p1 e => fun x h => snd (@endpoint_dact p (poly_times p0 p1) e x h)
       | endpoint_pair _ _ _ e1 e2 => fun x h => (endpoint_dact e1 x h, endpoint_dact e2 x h)
       | endpoint_inl p p0 _ e => fun x h => @endpoint_dact p p0 e x h
       | endpoint_inr p _ p1 e => fun x h => @endpoint_dact p p1 e x h
       end.

  (* If [h] commutes with constructors, then it commutes with all endpoints. *)
  Fixpoint endpoint_dact_compute
           {P Q : polynomial}
           (e : endpoint P Q)
    : forall (x : poly_act P A)
             (h : forall x, F x)
             (H : forall i u, h (c i u) = f i u (poly_dmap (C i) h u)),
      endpoint_dact e x (poly_dmap P h x) = poly_dmap Q h (endpoint_act e x)
    := match e with
       | endpoint_var _ => fun _ _ _ => reflexivity _
       | endpoint_const _ _ t => fun _ _ _ => reflexivity t
       | endpoint_constr _ i e' =>
         fun x h H => let u := (endpoint_act e' x) in
           ap (f i u) (endpoint_dact_compute e' x h H) @ (H i u)^
       | endpoint_fst _ _ _ e' =>
         fun x h H =>
           ap fst (endpoint_dact_compute e' x h H)
       | endpoint_snd _ _ _ e' =>
         fun x h H =>
           ap snd (endpoint_dact_compute e' x h H)
       | endpoint_pair _ _ _ e1 e2 =>
         fun x h H =>
           path_prod'
             (endpoint_dact_compute e1 x h H)
             (endpoint_dact_compute e2 x h H)
       | endpoint_inl _ _ _ e' => endpoint_dact_compute e'
       | endpoint_inr _ _ _ e' => endpoint_dact_compute e'
       end.

  (* A general HIT might have an arbitrary number of endpoints and therefore an arbitrarily
   nested point constructors. Our construction of a HIT presumes that there is a bound to
   the nesting. We define here what it means for an endpoint to have such a bound. *)
  Inductive endpoint_rank : forall {P Q : polynomial}, endpoint P Q -> nat -> Type :=
  | rank_var :
      forall {P : polynomial} (n : nat),
        endpoint_rank (@endpoint_var P) n
  | rank_const :
      forall {P : polynomial} {T : Type} (t : T) (n : nat),
        endpoint_rank (@endpoint_const P _ t) n
  | rank_constr :
      forall {P : polynomial} (i : I) (n : nat) (e : endpoint P (C i)),
        endpoint_rank e n -> endpoint_rank (endpoint_constr i e) (S n)
  | rank_fst :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P (poly_times Q R)),
        endpoint_rank e n -> endpoint_rank (endpoint_fst e) n
  | rank_snd :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P (poly_times Q R)),
        endpoint_rank e n -> endpoint_rank (endpoint_snd e) n
  | rank_inl :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P Q),
        endpoint_rank e n -> endpoint_rank (@endpoint_inl _ _ R e) n
  | rank_inr :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P R),
        endpoint_rank e n -> endpoint_rank (@endpoint_inr _ Q _ e) n.
End Endpoints.

Arguments endpoint {_} _ _ _.
Arguments endpoint_var {_ _} {_}.
Arguments endpoint_const {_ _} {_} {_} _.
Arguments endpoint_constr {_ _} {_} _ _ .
Arguments endpoint_fst {_ _} {_ _ _} _.
Arguments endpoint_snd {_ _} {_ _ _} _.
Arguments endpoint_pair {_ _} {_ _ _} _ _.
Arguments endpoint_inl {_ _} {_ _ _} _.
Arguments endpoint_inr {_ _} {_ _ _} _.

Arguments endpoint_act {_ _ _} _ {P Q} _ _.
Arguments endpoint_dact {I C A F} c _ {P Q} _ _ _.
Arguments endpoint_dact_compute {_ _ _} _ _ _ {P Q} _ _ _ _.

Arguments endpoint_rank {_} _ {_ _} _ _.

(* A HIT signature is specified by point constructors and path constructors.

   Note: we are allowing an arbitrary family of poitn and path construcrors.
         We will restrict them later on in existence theorem.
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
    sig_path_lhs : forall i, endpoint sig_point (sig_path_param i) poly_var ;
    sig_path_rhs : forall i, endpoint sig_point (sig_path_param i) poly_var
  }.

(* A HIT signature has rank [n] if all of its endpoints do. *)
Definition hit_rank Σ n :=
  (forall (j : sig_path_index Σ), endpoint_rank (sig_point Σ) (sig_path_lhs Σ j) n) *
  (forall (j : sig_path_index Σ), endpoint_rank (sig_point Σ) (sig_path_rhs Σ j) n).

Section HIT_Definition.

  (* We define HIT for signature [Σ]. *)
  Variable (Σ : hit_signature).

  (* The type of a lift of the point constructor [c] over a family [F]. *)
  Definition point_over
             {H : Type} (* the carrier type *)
             (F : H -> Type)
             (c : forall i, poly_act (sig_point Σ i) H -> H) (* point constructors *)
             (p : forall j u, endpoint_act c (sig_path_lhs Σ j) u =
                              endpoint_act c (sig_path_rhs Σ j) u) (* path constructors *)
    := forall (i : sig_point_index Σ) (u : poly_act (sig_point Σ i) H),
      poly_fam (sig_point Σ i) F u -> F (c i u).

  (* The type of a lift of the path constructor [p] over a family [F]. *)
  Definition path_over
             {H : Type}
             {F : H -> Type}
             {c : forall i, poly_act (sig_point Σ i) H -> H} (* point constructors *)
             {p : forall j u, endpoint_act c (sig_path_lhs Σ j) u =
                              endpoint_act c (sig_path_rhs Σ j) u} (* path constructors *)
             (c' : point_over F c p)
    := forall (j : sig_path_index Σ)
              (x : poly_act (sig_path_param Σ j) H)
              (h : poly_fam (sig_path_param Σ j) F x),
      transport _ (p j x) (endpoint_dact c c' (sig_path_lhs Σ j) x h) =
      endpoint_dact c c' (sig_path_rhs Σ j) x h.

  (* It is tricky to phrase the computation rule for paths, so we phrase an auxiliary lemma
   that lets us construct the type of the path computation rule interactively. *)
  Definition hit_path_beta_eq
             (H : Type) (* the carrier type *)
             (c : forall i, poly_act (sig_point Σ i) H -> H) (* point constructors *)
             (p : forall j u, endpoint_act c (sig_path_lhs Σ j) u =
                              endpoint_act c (sig_path_rhs Σ j) u) (* path constructors *)
             (E : (* the eliminator *)
                forall (F : H -> Type)
                       (c' : point_over F c p)
                       (p' : path_over c'),
                forall (x : H), F x)
             (point_beta : (* the point computation rule *)
                forall (F : H -> Type)
                       (c' : point_over F c p)
                       (p' : path_over c')
                       i (t : poly_act (sig_point Σ i) H),
                  E F c' p' (c i t) = c' i t (poly_dmap (sig_point Σ i) (E F c' p') t)) :
    Type.
  Proof.
    simple refine (forall (F : H -> Type) (j : sig_path_index Σ)
                          (c' : point_over F c p)
                          (p' : path_over c')
                          (k : sig_path_index Σ)
                          (t : poly_act (sig_path_param Σ k) H), _).
    (* We want an equation between [α] and [β], but their types do not match, so a transport
     is required on each side of the equation. *)
    pose (α := apD (E F c' p') (p k t)).
    pose (β := p' k t (poly_dmap _ (E F c' p') t)).
    simpl in β.
    (* the path along which we will transport lhs *)
    assert (q_lhs : endpoint_dact c c' (sig_path_lhs Σ k) t (poly_dmap (sig_path_param Σ k) (E F c' p') t) =
                    E F c' p' (endpoint_act c (sig_path_lhs Σ k) t)).
    { apply (endpoint_dact_compute F c c' (sig_path_lhs Σ k) t), point_beta. }
    (* the path along which we will transport rhs *)
    assert (q_rhs : endpoint_dact c c' (sig_path_rhs Σ k) t (poly_dmap (sig_path_param Σ k) (E F c' p') t) =
                    E F c' p' (endpoint_act c (sig_path_rhs Σ k) t)).
    { apply (endpoint_dact_compute F c c' (sig_path_rhs Σ k) t), point_beta. }
    pose (β' := transport
                  (fun z => transport F (p k t) z =
                            endpoint_dact c c' (sig_path_rhs Σ k) t (poly_dmap (sig_path_param Σ k) (E F c' p') t))

                  q_lhs β).
    simpl in β'.
    pose (β'' := transport
                   (fun z => transport F (p k t) (E F c' p' (endpoint_act c (sig_path_lhs Σ k) t)) = z)
                   q_rhs β').
    exact (α = β'').
  Defined.

  Structure HIT :=
    {
      (* the carrier of the HIT *)
      hit_carrier :> Type ;

      (* the point constructor *)
      hit_point : forall i, poly_act (sig_point Σ i) hit_carrier -> hit_carrier ;

      (* path constructors *)
      hit_path : forall j u, endpoint_act hit_point (sig_path_lhs Σ j) u =
                             endpoint_act hit_point (sig_path_rhs Σ j) u ;

      (* the eliminator *)
      hit_ind :
        forall (F : hit_carrier -> Type)
               (c : point_over F hit_point hit_path)
               (p : path_over c)
               (x : hit_carrier),
          F x ;

      (* computation rule for points *)
      hit_point_beta :
        forall (F : hit_carrier -> Type)
               (c : point_over F hit_point hit_path)
               (p : path_over c)
               (i : sig_point_index Σ)
               (t : poly_act (sig_point Σ i) hit_carrier),
          hit_ind F c p (hit_point i t) =
          c i t (poly_dmap (sig_point Σ i) (hit_ind F c p) t) ;

      (* computation rule for paths *)
      hit_path_beta :
        hit_path_beta_eq hit_carrier hit_point hit_path hit_ind hit_point_beta
    }.
End HIT_Definition.

Arguments hit_point {_ _} _ _.
Arguments hit_path {_ _} _ _.
Arguments hit_ind {_ _} _ _ _ _.

Section HIT_Primitive_Recursion.
  (** The non-dependent recursion principle follows from the induction principle. *)

  Variable Σ : hit_signature. (* The HIT signature. *)

  (** We give a special name to [endpoint_dact] applied to a constant family.
      To be used for the non-dependent recursion principle. *)
  Definition endpoint_dact_nondep
             {I : Type} {C : I -> polynomial} {A : Type} {B : Type}
             (c : forall i : I, poly_act (C i) A -> A)
             (f : forall i (u : poly_act (C i) A), poly_fam (C i) (fun _ => B) u -> B)
             {P Q : polynomial}
             (e : endpoint C P Q) (x : poly_act P A) (h : poly_fam P (fun _ => B) x)
    := @endpoint_dact I C A (fun _ => B) c f P Q e x h.

  Section Methods.
    Variable (H : HIT Σ) (* the carrier type *)
             (A : Type) (* the target type *)
             (c : forall i, poly_act (sig_point Σ i) H -> H) (* point constructors *)
             (p : forall j u,
                 endpoint_act c (sig_path_lhs Σ j) u
                 =
                 endpoint_act c (sig_path_rhs Σ j) u). (* path constructors *)

    (* The non-dependent version of a lift of a point constructor, to be used in the
     non-dependent recursion principle. *)
    Definition point_over_nondep
      := forall (i : sig_point_index Σ) (u : poly_act (sig_point Σ i) H),
        poly_fam (sig_point Σ i) (fun _ => A) u -> A.

    (* The non-dependent version of a lift of a path constructor, to be used in the
     non-dependent recursion principle. *)
    Definition path_over_nondep (c' : point_over_nondep)
      := forall (j : sig_path_index Σ)
                (x : poly_act (sig_path_param Σ j) H)
                (h : poly_fam (sig_path_param Σ j) (fun _ => A) x),
        transport _ (p j x) (endpoint_dact_nondep c c' (sig_path_lhs Σ j) x h)
        =
        endpoint_dact_nondep c c' (sig_path_rhs Σ j) x h.
  End Methods.

  Variable (H : HIT Σ) (A : Type)
           (c : point_over_nondep H A)
           (p : path_over_nondep H A (@hit_point Σ H) hit_path c).

  Definition hit_primrec : H -> A := hit_ind (fun (x : H) => _) c p.

  Definition hit_point_primrec_beta
          (i : sig_point_index Σ)
          (u : poly_act (sig_point Σ i) H)
          (x : poly_fam (sig_point Σ i) (fun (x : H) => A) u)
    : hit_primrec (hit_point i u)
      =
      c i u (poly_dmap (sig_point Σ i) hit_primrec u)
    := hit_point_beta Σ H _ c p i u.

  Section beta_path.
    Variable (j : sig_path_index Σ)
             (u : poly_act (sig_path_param Σ j) H)
             (x : poly_fam (sig_path_param Σ j) (fun _ => A) u).

    Definition endpoint_compute_lhs
      : endpoint_dact_nondep
          hit_point c (sig_path_lhs Σ j) u
          (poly_dmap (sig_path_param Σ j) hit_primrec u)
        =
        hit_primrec (endpoint_act hit_point (sig_path_lhs Σ j) u)
      := endpoint_dact_compute _ _ _ _ _ _ (hit_point_beta _ H _ c p).
      
    Definition endpoint_transport_compute_lhs
      := ap (transport (fun _ : H => A) (hit_path j u)) endpoint_compute_lhs.

    Definition endpoint_compute_rhs
      : endpoint_dact_nondep
          hit_point c (sig_path_rhs Σ j) u
          (poly_dmap (sig_path_param Σ j) hit_primrec u)
        =
        hit_primrec (endpoint_act hit_point (sig_path_rhs Σ j) u)
      := endpoint_dact_compute _ _ _ _ _ _ (hit_point_beta _ H _ c p).

    Definition endpoint_const_compute_lhs
      := transport_const (hit_path j u) _ @ endpoint_compute_lhs.

    Theorem hit_path_primrec_beta'
      : apD hit_primrec (hit_path j u)
        =
        endpoint_transport_compute_lhs^
        @ p j u (poly_dmap (sig_path_param Σ j) hit_primrec u)
          @ endpoint_compute_rhs.
    Proof.
      unfold hit_primrec.
      refine (hit_path_beta _ _ _ j _ _ _ _ @ _).
      rewrite !transport_paths_FlFr.
      hott_simpl.
    Defined.

    Theorem hit_path_primrec_beta
      : ap hit_primrec (hit_path j u)
        =
        endpoint_const_compute_lhs^
        @ p j u (poly_dmap (sig_path_param Σ j) hit_primrec u)
          @ endpoint_compute_rhs.
    Proof.
      eapply (cancelL (transport_const (hit_path j u) _)).
      simple refine ((apD_const _ _)^ @ _).
      rewrite hit_path_primrec_beta'.
      hott_simpl.
      repeat f_ap.
      rewrite inv_pp.
      induction endpoint_compute_lhs.
      hott_simpl.
    Defined.      
  End beta_path.
End HIT_Primitive_Recursion.

Section HIT_Recursion.
  (** The non-dependent recursion principle follows from the induction principle. *)

  Variable (Σ : hit_signature). (* The HIT signature. *)

  Definition fam_const
             {A B : Type}
             {P : polynomial}
             {p : poly_act P A}
    : poly_fam P (fun _ : A => B) p -> poly_act P B.
  Proof.
    induction P.
    - apply idmap.
    - apply idmap.
    - intros [x1 x2].
      refine (IHP1 (fst p) x1, IHP2 (snd p) x2).
    - intros x.
      destruct p as [p | p].
      * apply (inl (IHP1 p x)).
      * apply (inr (IHP2 p x)).
  Defined.

  (** We give a special name to [endpoint_dact] for the recursion principle. *)
  Definition endpoint_dact_rec
             {I : Type} {C : I -> polynomial} {A : Type} {B : Type}
             (c : forall i : I, poly_act (C i) A -> A)
             (f : forall i, poly_act (C i) B -> B)
             {P Q : polynomial}
             (e : endpoint C P Q) (x : poly_act P A) (h : poly_fam P (fun _ => B) x)
    := @endpoint_dact I C A (fun _ => B) c (fun i _ u => f i (fam_const u)) P Q e x h.

  Definition endpoint_dact_const
        {I : Type} {C : I -> polynomial} {A : Type} {B : Type}
        (c : forall i : I, poly_act (C i) A -> A)
        (f : forall i, poly_act (C i) B -> B)
        {P Q : polynomial}
        (e : endpoint C P Q) (x : poly_act P A) (h : poly_fam P (fun _ => B) x)
    : fam_const (@endpoint_dact I C A _ c (fun i _ u => f i (fam_const u)) P Q e x h)
      =
      @endpoint_act I C B f P Q e (fam_const h).
  Proof.
    induction e ; simpl in *.
    - reflexivity.
    - reflexivity.
    - refine (ap (f i) (IHe _ _)).
    - refine (ap fst (IHe x h)).
    - refine (ap snd (IHe x h)).
    - refine (path_prod' (IHe1 x h) (IHe2 x h)).
    - refine (ap inl (IHe x h)).
    - refine (ap inr (IHe x h)).
  Defined.

  Variable (H : HIT Σ)
           (A : Type).

  (* The non-dependent version of a lift of a point constructor, to be used in the
     non-dependent recursion principle. *)
  Definition point_over_rec
    := forall (i : sig_point_index Σ), poly_act (sig_point Σ i) A -> A.

  (* The non-dependet version of a lift of a path constructor, to be used in the
     non-dependent recursion principle. *)
  Definition path_over_rec_help (cY : point_over_rec)
    := forall (j : sig_path_index Σ)
              (x : poly_act (sig_path_param Σ j) H)
              (h : poly_fam (sig_path_param Σ j) (fun _ => A) x),
      endpoint_dact_rec hit_point cY (sig_path_lhs Σ j) x h =
      endpoint_dact_rec hit_point cY (sig_path_rhs Σ j) x h.

  Definition path_over_rec (cY : point_over_rec)
    := forall (j : sig_path_index Σ)
              (x : poly_act (sig_path_param Σ j) A),
      endpoint_act cY (sig_path_lhs Σ j) x =
      endpoint_act cY (sig_path_rhs Σ j) x.
  
  Variable (cY : point_over_rec)
           (pY_rec : path_over_rec cY).

  Definition pY : path_over_rec_help cY :=
    fun j x h =>
      endpoint_dact_const hit_point cY _ _ _
                          @ pY_rec j (fam_const h)
                          @ (endpoint_dact_const hit_point cY _ _ _ )^.
    
  Definition cY' : point_over_nondep Σ H A
    := fun i _ x => cY i (fam_const x).

  Definition pY' : @path_over_nondep Σ H A hit_point hit_path cY'.
  Proof.
    intros j x h ; simpl.
    refine (transport_const _ _ @ _).
    pose (pY j x).
    apply pY.
  Defined.

  Definition hit_rec : H -> A := hit_primrec Σ H A cY' pY'.

  Theorem hit_point_rec_beta
          (i : sig_point_index Σ)
          (u : poly_act (sig_point Σ i) H)
    : hit_rec (hit_point i u)
      =
      cY i (poly_map (sig_point Σ i) hit_rec u).
  Proof.
    unfold hit_rec.
    rewrite hit_point_primrec_beta.
    - unfold cY'.
      f_ap.
      induction (sig_point Σ i) ; simpl ; try reflexivity.
      * rewrite IHp1, IHp2.
        reflexivity.
      * destruct u ; rewrite IHp1 || rewrite IHp2 ; try f_ap ; auto.
    - induction (sig_point Σ i) ; simpl in *.
      * apply (hit_rec u).
      * apply u.
      * refine (IHp1 (fst u), IHp2 (snd u)).
      * destruct u.
        ** apply IHp1 ; auto.
        ** apply IHp2 ; auto.
  Defined.

  Section beta_path.
    Variable (j : sig_path_index Σ)
             (u : poly_act (sig_path_param Σ j) H).

    Definition t5
      : endpoint_dact_rec hit_point cY (sig_path_lhs Σ j) u
                          (poly_dmap (sig_path_param Σ j) hit_rec u)
        =
        hit_rec (endpoint_act hit_point (sig_path_lhs Σ j) u)
      := (transport_const _ _)^ @ endpoint_const_compute_lhs Σ H A cY' pY' j u.

    Definition t6
      : endpoint_dact_rec hit_point cY (sig_path_rhs Σ j) u
                          (poly_dmap (sig_path_param Σ j) hit_rec u)
        =
        hit_rec (endpoint_act hit_point (sig_path_rhs Σ j) u)
      := endpoint_compute_rhs Σ H A cY' pY' j u.
    
    Theorem hit_rec_beta_path      
      : ap hit_rec (hit_path j u)
        =
        t5^ @ pY j u (poly_dmap (sig_path_param Σ j) hit_rec u) @ t6.
    Proof.
      unfold hit_rec.
      rewrite hit_path_primrec_beta.
      unfold pY', t5.
      rewrite inv_pp.
      hott_simpl.
    Defined.
  End beta_path.
End HIT_Recursion.