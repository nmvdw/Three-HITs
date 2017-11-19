Require Import HoTT.
Require Import hit_structure polynomial.

(* Example: circle *)
Section Circle.
  Definition circle_signature :=
    {|
      sig_point_index := Unit ;
      sig_point := (fun _ => poly_const Unit) ;
      sig_path_index := Unit ;
      sig_path_param := (fun _ => poly_const Unit) ;
      sig_path_lhs := (fun _ => endpoint_constr tt endpoint_var) ;
      sig_path_rhs := (fun _ => endpoint_constr tt endpoint_var)
    |}.

  (* Example: the HoTT library circle is a HIT *)
  Definition circle_hit : HIT circle_signature.
  Proof.
    simple refine {| hit_carrier := S1 ;
                     hit_point := (fun _ _ => base) ;
                     hit_path := (fun _ _ => _ ) |}.
    - exact loop.
    - intros F c f x.
      now apply (S1_ind F (c tt tt tt)), (f tt).
    - intros F c p [] [] ; reflexivity.
    - intros F [] c p [] [].
      apply S1_ind_beta_loop.
  Defined.

  Definition S1_rec (A : Type) (a : A) (p : a = a) : S1 -> A
    := hit_rec circle_signature circle_hit A (fun _ _ => a) (fun _ _ => p).

  Lemma S1_rec_beta_point (A : Type) (a : A) (p : a = a)
    : S1_rec A a p base = a.
  Proof.
    unfold S1_rec.
    rewrite (@hit_point_rec_beta circle_signature circle_hit A _ _ tt tt).
    reflexivity.
  Defined.    

  Lemma circle_rec_beta_loop (A : Type) (x : A) (p : x = x) :
    ap (S1_rec A x p) (@hit_path circle_signature circle_hit tt tt) = p.
  Proof.
    unfold S1_rec.
    rewrite (@hit_rec_beta_path circle_signature circle_hit A _ _ tt tt).
    unfold t5, t6.
    hott_simpl.
  Defined.
End Circle.

(* Example: natural numbers *)
Section NaturalNumbers.
  Definition nat_signature :=
    {|
      sig_point_index := Bool ;
      sig_point := (fun b => if b then poly_const Unit else poly_var) ;
      sig_path_index := Empty ;
      sig_path_param := Empty_rect _ ;
      sig_path_lhs := Empty_rect _ ;
      sig_path_rhs := Empty_rect _
    |}.

  (* Example: nat is a hit. *)
  Definition nat_hit : HIT nat_signature.
  Proof.
    simple refine {| hit_carrier := nat |}.
    - intros [ | ]; cbn.
      + intros _ ; exact 0.
      + exact S.
    - intros i ; elim i.
    - intros F c p x.
      induction x as [| n y].
      + exact (c true tt tt).
      + apply (c false n y).
    - intros F c p [ | ] [] ; reflexivity.
    - intros _ [].
  Defined.

  (* The usual recursion principle for numbers is indeed just `hit_rec`. *)
  Lemma nat_rec (A : Type) (x : A) (f : A -> A) : nat -> A.
  Proof.
    simple refine (hit_rec nat_signature nat_hit A _ _).
    - unfold point_over_rec.
      intros [ | ] ; simpl.
      * apply (fun _ => x).
      * apply f.
    - unfold path_over_rec.
      intros [].
  Defined.

  Lemma nat_rec_beta_Z (A : Type) (x : A) (f : A -> A)
    : nat_rec A x f 0 = x.
  Proof.
    unfold nat_rec.
    rewrite (@hit_point_rec_beta nat_signature nat_hit A _ _ true tt).
    reflexivity.
  Defined.

  Lemma nat_rec_beta_S (A : Type) (x : A) (f : A -> A) (n : nat)
    : nat_rec A x f (S n) = f(nat_rec A x f n).
  Proof.
    unfold nat_rec.
    rewrite (@hit_point_rec_beta nat_signature nat_hit A _ _ false n).
    reflexivity.
  Defined.
End NaturalNumbers.

(* Example: susupension *)
Section Suspension.
  Variable (A : Type).

  Definition suspension_signature :=
    {|
      sig_point_index := Bool ;
      sig_point := (fun _ => poly_const Unit) ;
      sig_path_index := Unit ;
      sig_path_param := (fun _ => poly_const A) ;
      sig_path_lhs := (fun _ => endpoint_constr false (endpoint_const tt)) ;
      sig_path_rhs := (fun _ => endpoint_constr true (endpoint_const tt))
    |}.

  Definition suspension_hit : HIT suspension_signature.
  Proof.
    simple refine {| hit_carrier := Susp A |}.
    - intros [_|_] ; [exact South | exact North].
    - intros [] x ; exact (merid x).
    - intros F c f x.
      apply (Susp_ind F (c false tt tt) (c true tt tt)).
      intro a.
      apply (f tt _ a).
    - intros F c p [|] [] ; reflexivity.
    - intros F [] c p [] a.
      simpl in *.
      apply Susp_ind_beta_merid with (x := a).
  Defined.

  Variable (Y : Type)
           (n : Y) (s : Y)
           (m : A -> n = s).

  Definition suspension_rec : Susp A -> Y.
  Proof.
    simple refine (hit_rec suspension_signature suspension_hit Y _ _).
    - intros i x ; simpl in *.
      destruct i.
      * apply s.
      * apply n.
    - intros j x ; simpl in *.
      apply (m x).
  Defined.

  Lemma suspension_beta_n : suspension_rec North = n.
  Proof.
    unfold suspension_rec.
    rewrite (@hit_point_rec_beta suspension_signature suspension_hit Y _ _ false tt).
    reflexivity.
  Defined.    

  Lemma suspension_beta_s : suspension_rec South = s.
  Proof.
    unfold suspension_rec.
    rewrite (@hit_point_rec_beta suspension_signature suspension_hit Y _ _ true tt).
    reflexivity.
  Defined.

  Lemma suspension_beta_m (a : A)
    : ap suspension_rec (@hit_path suspension_signature suspension_hit tt a) = m a.
  Proof.
    unfold suspension_rec.
    rewrite (@hit_rec_beta_path suspension_signature suspension_hit Y _ _ tt a).
    unfold t5, t6.
    hott_simpl.
  Defined.
End Suspension.

(* Example: propositional truncation *)
Section Propositional_Truncation.
  Variable (A : Type).
  
  Definition trunc_signature :=
    {|
      sig_point_index := Unit ;
      sig_point := (fun _ => poly_const A) ;
      sig_path_index := Unit ;
      sig_path_param := (fun _ => poly_times poly_var poly_var) ;
      sig_path_lhs := (fun _ => endpoint_fst endpoint_var) ;
      sig_path_rhs := (fun _ => endpoint_snd endpoint_var)
    |}.

  Definition trunc_hit : HIT trunc_signature.
  Proof.
    simple refine {| hit_carrier := Trunc (-1) A |}.
    - intros [ ] ; simpl.
      apply tr.
    - intros [] x ; simpl in *.
      apply path_ishprop.
    - intros F c f x ; simpl in *.
      simple refine (Trunc_ind F _ _).
      * intros a.
        apply hprop_allpath.
        intros y1 y2.
        specialize (f tt (a, a) (y1, y2)).
        simpl in f.
        assert (path_ishprop a a = idpath) as X.
        { apply path_ishprop. }
        rewrite X in f.
        apply f.
      * intros a.
        refine (c tt _ a).      
    - intros F c p [] t.
      reflexivity.
    - intros F [] c p [] a.
      simpl in *.
      assert (IsHProp (F (snd a))).
      {
        apply hprop_allpath.
        intros y1 y2.
        specialize (p tt (snd a, snd a) (y1, y2)).
        simpl in p.
        assert (path_ishprop (snd a) (snd a) = idpath) as X.
        { apply path_ishprop. }
        rewrite X in p.
        apply p.
      }
      refine (path_ishprop _ _).
  Defined.

  Variable (Y : Type)
           (trY : A -> Y)
           (pY : forall (x y : Y), x = y).

  Definition trunc_rec : Trunc (-1) A -> Y.
  Proof.
    simple refine (hit_rec trunc_signature trunc_hit Y _ _).
    - intros i ; simpl in *.
      apply trY.
    - intros j x ; simpl in *.
      apply pY.
  Defined.

  Lemma trunc_beta_n (a : A) : trunc_rec (tr a) = trY a.
  Proof.
    unfold trunc_rec.
    rewrite (@hit_point_rec_beta trunc_signature trunc_hit Y _ _ tt a).
    reflexivity.
  Defined.    

  Lemma trunc_beta_m (x y : Trunc (-1) A)
    : ap trunc_rec (@hit_path trunc_signature trunc_hit tt (x,y))
      = pY (trunc_rec x) (trunc_rec y).
  Proof.
    unfold trunc_rec.
    rewrite (@hit_rec_beta_path trunc_signature trunc_hit Y _ _ tt (x,y)).
    unfold t5, t6.
    hott_simpl.
  Defined.
End Propositional_Truncation.