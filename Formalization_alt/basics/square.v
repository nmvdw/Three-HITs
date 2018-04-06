Require Import HoTT.
Require Import heterogeneous_equality path_over.

(** Squares represents heterogeneous equalities between paths.
    A square has 4 sides `t`, `l`, `r`, `d` and it represents `l^ @ t @ r = d`.
    One way to define it, is using an inductive type with one constructor.
 *)
Inductive square {A : Type} : 
  forall {lt rt ld rd : A}
         (t : lt = rt)
         (l : ld = lt) (r : rd = rt)
         (d : ld = rd),
    Type
  := id_square : forall {a : A},
      square (@idpath _ a) idpath idpath (@idpath _ a).

(** We can also use another constructor. *)
Inductive square_lr  {A : Type} : 
  forall {lt rt ld rd : A}
         (t : lt = rt)
         (l : ld = lt) (r : rd = rt)
         (d : ld = rd),
    Type
  := id_square_lr : forall {t d : A}
                           {l : d = t} {r : d = t}
                           (h : l = r),
      square_lr idpath l r idpath.

Section equivalences.
  (** An equivalent definition of `square t l r d` is `l @ t = d @ r`.
      So, it is equivalent to a homotopy.
   *)
  Definition square_to_path
             {A : Type}
             {lt rt ld rd : A}
             {t : lt = rt}
             {l : ld = lt} {r : rd = rt}
             {d : ld = rd}
             (s : square t l r d)
    : l @ t = d @ r
    := match s with
       | id_square a => idpath
       end.

  Definition path_to_square
             {A : Type}
             {lt rt ld rd : A}
             {t : lt = rt}
             {l : ld = lt} {r : rd = rt}
             {d : ld = rd}
             (p : l @ t = d @ r)
    : square t l r d.
  Proof.
    induction t, l, d.
    exact (transport
             (fun z => square 1 1 z 1)
             (cancelL idpath idpath r p)
             id_square).
  Defined.

  Global Instance square_to_path_is_equiv
         {A : Type}
         {lt rt ld rd : A}
         {t : lt = rt}
         {l : ld = lt} {r : rd = rt}
         {d : ld = rd}
    : IsEquiv (@square_to_path _ _ _ _ _ t l r d).
  Proof.
    simple refine (isequiv_adjointify _ path_to_square _ _).
    - intros p.
      induction t, l, d ; cbn.
      refine (_ @ @eissect _ _ (cancelL 1 1 r) (isequiv_cancelL _ _ _) _).
      induction (cancelL idpath idpath r p) ; cbn.
      reflexivity.
    - intros x.
      induction x ; reflexivity.
  Defined.

  (** The two inductive definitions of squares are equivalent. *)
  Definition square_to_square_lr
             {A : Type}
             {lt rt ld rd : A}
             {t : lt = rt}
             {l : ld = lt} {r : rd = rt}
             {d : ld = rd}
             (s : square t l r d)             
    : square_lr t l r d
    := match s with
       | id_square _ => id_square_lr idpath
       end.

  Definition square_lr_to_square
             {A : Type}
             {lt rt ld rd : A}
             {t : lt = rt}
             {l : ld = lt} {r : rd = rt}
             {d : ld = rd}
             (s : square_lr t l r d)
    : square t l r d.
  Proof.
    induction s, l.
    exact (transport
             (fun z => square idpath idpath z idpath)
             h
             id_square).
  Defined.

  Global Instance square_to_square_lr_isequiv
         {A : Type}
         {lt rt ld rd : A}
         {t : lt = rt}
         {l : ld = lt} {r : rd = rt}
         {d : ld = rd}
    : IsEquiv (@square_to_square_lr _ _ _ _ _ t l r d).
  Proof.
    simple refine (isequiv_adjointify _ square_lr_to_square _ _).
    - intros x.
      induction x, l, h ; reflexivity.
    - intros x ; induction x.
      reflexivity.
  Defined.

  (** A square is a path over a pair of paths in a family of paths. *)
  Definition square_to_path_over
             {A : Type}
             {lt rt ld rd : A}
             {t : lt = rt}
             {l : ld = lt} {r : rd = rt}
             {d : ld = rd}
             (s : square t l r d)             
    : path_over (fun (x : A * A) => fst x = snd x) (path_prod' d t) l r
    := match s with
       | id_square a => path_over_id _
       end.

  Definition path_over_to_square
             {A : Type}
             {lt rt ld rd : A}
             {t : lt = rt}
             {l : ld = lt} {r : rd = rt}
             {d : ld = rd}
             (q : path_over (fun (x : A * A) => fst x = snd x) (path_prod' d t) l r)
    : square t l r d.
  Proof.
    induction t, l, d.
    exact (transport
             (fun z => square idpath idpath z idpath)
             (path_over_to_path q)
             id_square).
  Defined.

  Global Instance square_to_path_over_is_equiv
         {A : Type}
         {lt rt ld rd : A}
         {t : lt = rt}
         {l : ld = lt} {r : rd = rt}
         {d : ld = rd}
    : IsEquiv (@square_to_path_over A lt rt ld rd t l r d).
  Proof.
    simple refine (isequiv_adjointify _ (@path_over_to_square A _ _ _ _ t l r d) _ _).
    - intros x ; induction t, l, d ; cbn in *.
      refine (_ @ eissect path_over_to_path x).
      induction (path_over_to_path x).
      reflexivity.
    - intros x ; induction x.
      reflexivity.
  Defined.
End equivalences.

Section operations.
  (** We have two identity paths.
      The first one is between the top and bottom side.
   *)
  Definition hrefl
             {A : Type} {a b : A}
             (p : a = b)
    : square p idpath idpath p
    := match p with
       | idpath => id_square
       end.

  (** The second identity is between the left and right side. *)
  Definition vrefl
             {A : Type} {a b : A}
             (p : a = b)
    : square idpath p p idpath
    := match p with
       | idpath => id_square
       end.

  (** We can apply maps to squares. *)
  Definition ap_square
             {A B : Type} (f : A -> B)
             {lt rt ld rd : A}
             {t : lt = rt}
             {l : ld = lt} {r : rd = rt}
             {d : ld = rd}
             (s : square t l r d)
    : square (ap f t) (ap f l) (ap f r) (ap f d)
    := match s with
       | id_square _ => id_square
       end.

  (** We can make squares of pairs. *)
  Definition pair_square
             {A B : Type}
             {lta rta lda rda : A}
             {ta : lta = rta}
             {la : lda = lta} {ra : rda = rta}
             {da : lda = rda}
             {ltb rtb ldb rdb : B}
             {tb : ltb = rtb}
             {lb : ldb = ltb} {rb : rdb = rtb}
             {db : ldb = rdb}
             (sa : square ta la ra da)
             (sb : square tb lb rb db)
    : square (path_prod' ta tb)
             (path_prod' la lb)
             (path_prod' ra rb)
             (path_prod' da db)
    := match sa, sb with
       | id_square _, id_square _ => id_square
       end.

  (** We can move a square along paths in each coordinate. *)
  Definition whisker_square
             {A : Type}
             {lt rt ld rd : A}
             {t₁ t₂ : lt = rt}
             {l₁ l₂ : ld = lt} {r₁ r₂ : rd = rt}
             {d₁ d₂ : ld = rd}
             (pt : t₁ = t₂)
             (pl : l₁ = l₂) (pr : r₁ = r₂)
             (pd : d₁ = d₂)
             (s : square t₁ l₁ r₁ d₁)
    : square t₂ l₂ r₂ d₂.
  Proof.
    induction s.
    refine (transport (square t₂ l₂ r₂) pd _).
    refine (transport (fun z => square t₂ l₂ z _) pr _).
    refine (transport (fun z => square t₂ z _ _) pl _).
    exact (transport (fun z => square z _ _ _) pt id_square).
  Defined.

  (** Vertical composition of squares. *)
  Definition compose_square_v
             {A : Type}
             {lt rt : A}
             {lm rm : A}
             {ld rd : A}
             {t : lt = rt}
             {l₁ : lm = lt} {r₁ : rm = rt}
             {m : lm = rm}
             {l₂ : ld = lm} {r₂ : rd = rm}
             {d : ld = rd}
             (s₁ : square t l₁ r₁ m)
             (s₂ : square m l₂ r₂ d)
    : square t (l₂ @ l₁) (r₂ @ r₁) d.
  Proof.
    induction s₁.
    exact (whisker_square
             idpath
             (concat_p1 l₂)^
             (concat_p1 r₂)^
             idpath
             s₂).
  Defined.

  (** Horizontal composition of squares. *)
  Definition compose_square_h
             {A : Type}
             {lt mt rt : A}
             {ld md rd : A}
             {t₁ : lt = mt} {t₂ : mt = rt}
             {l : ld = lt} {m : md = mt} {r : rd = rt}
             {d₁ : ld = md} {d₂ : md = rd}
             (s₁ : square t₁ l m d₁)
             (s₂ : square t₂ m r d₂)
    : square (t₁ @ t₂) l r (d₁ @ d₂).
  Proof.
    induction s₁.
    exact (whisker_square
             ((concat_1p t₂)^)
             idpath
             idpath
             ((concat_1p d₂)^)
             s₂).
  Defined.

  (** We can rotate squares.
      This gives an equivalence.
   *)
  Definition square_symmetry
             {A : Type}
             {lt rt ld rd : A}
             {t : lt = rt}
             {l : ld = lt} {r : rd = rt}
             {d : ld = rd}
             (s : square t l r d)
    : square r d t l
    := match s with
       | id_square _ => id_square
       end.

  Global Instance square_symmetry_isequiv
         {A : Type}
         {lt rt ld rd : A}
         {t : lt = rt}
         {l : ld = lt} {r : rd = rt}
         {d : ld = rd}
    : IsEquiv (@square_symmetry A lt rt ld rd t l r d).
  Proof.
    simple refine (isequiv_adjointify _ square_symmetry _ _) ;
      intro x ; induction x ; reflexivity.
  Defined.

  (** If one side of the square is missing, then we can fill it.
      This is a Kan-filling.
   *)
  Definition fill_square_top
             {A : Type}
             {lt rt ld rd : A}
             {l : ld = lt} {r : rd = rt}
             {d : ld = rd}
    : {t : lt = rt & square t l r d}
    := (l^ @ d @ r;
          path_to_square ((concat_p_pp _ _ _)
                            @ (ap (fun z => z @ _) (concat_p_pp _ _ _))
                            @ (ap (fun z => (z @ _) @ _) (concat_pV l))
                            @ (ap (fun z => z @ _) (concat_1p _)))).

  Definition fill_square_left
             {A : Type}
             {lt rt ld rd : A}
             {t : lt = rt}
             {r : rd = rt}
             {d : ld = rd}
    : {l : ld = lt & square t l r d}
    := (d @ r @ t^;
          path_to_square ((ap (fun z => z @ _) (concat_pp_p _ _ _))
                            @ (concat_pp_p _ _ _)
                            @ (ap (fun z => _ @ z) (concat_pp_p _ _ _))
                            @ (ap (fun z => _ @ (_ @ z)) (concat_Vp _))
                            @ (ap (fun z => _ @ z) (concat_p1 _)))).

  Definition fill_square_right
             {A : Type}
             {lt rt ld rd : A}
             {t : lt = rt}
             {l : ld = lt}
             {d : ld = rd}
    : {r : rd = rt & square t l r d}
    := (d^ @ l @ t;
          path_to_square ((ap (fun z => z @ _) (concat_1p _)^)
                            @ (ap (fun z => (z @ _) @ _) (concat_pV _)^)
                            @ (ap (fun z => z @ _) (concat_p_pp _ _ _)^)
                            @ (concat_p_pp _ _ _)^)).

  Definition fill_square_down
             {A : Type}
             {lt rt ld rd : A}
             {t : lt = rt}
             {l : ld = lt} {r : rd = rt}
    : {d : ld = rd & square t l r d}
    := (l @ t @ r^;
          path_to_square ((ap (fun z => _ @ z) (concat_p1 _)^)
                            @ (ap (fun z => (_ @ (_ @ z))) (concat_Vp _)^)
                            @ (ap (fun z => _ @ z) (concat_pp_p _ _ _)^)
                            @ ((concat_pp_p _ _ _)^)
                            @ (ap (fun z => z @ _) (concat_pp_p _ _ _)^))).

  (** Next we want look at squares of the form `square t (ap f p) (ap g p) d`.
      These are the same as paths over `p` in the family `f z = g z.
      For that, we first need some lemmata.
   *)
  Definition path_to_transport
             {A B : Type} {f g : A -> B}
             {a₁ a₂ : A} {p : a₁ = a₂}
    : forall {l : f a₁ = g a₁} {r : f a₂ = g a₂} (q : ap f p @ r = l @ ap g p),
      transport (fun z : A => f z = g z) p l = r
    := match p with
       | idpath => fun l r q => (concat_p1 l)^ @ q^ @ concat_1p r
       end.

  Definition transport_to_path
             {A B : Type} {f g : A -> B}
             {a₁ a₂ : A} {p : a₁ = a₂}
    : forall {l : f a₁ = g a₁} {r : f a₂ = g a₂}
             (q : transport (fun z : A => f z = g z) p l = r),
      ap f p @ r = l @ ap g p
    := match p with
       | idpath => fun l r q => concat_1p r @ q^ @ (concat_p1 l)^
       end.

  Global Instance path_to_transport_is_equiv
         {A B : Type} {f g : A -> B}
         {a₁ a₂ : A} {p : a₁ = a₂}
         {l : f a₁ = g a₁} {r : f a₂ = g a₂}
    : IsEquiv (@path_to_transport A B f g a₁ a₂ p l r).
  Proof.
    simple refine (isequiv_adjointify _ transport_to_path _ _).
    - intros x.
      induction x, p ; cbn.
      rewrite !inv_pp, inv_V ; cbn.
      hott_simpl.
    - intros x.
      induction p ; cbn in * ; induction l ; cbn in *.
      rewrite !inv_pp, !inv_V ; cbn.
      hott_simpl.
  Defined.
  
  Definition map_path_over
             {A B : Type} {f g : A -> B}
             {a₁ a₂ : A} {p : a₁ = a₂}
             {l : f a₁ = g a₁} {r : f a₂ = g a₂}
    : square r (ap f p) (ap g p) l -> path_over (fun z => f z = g z) p l r
    := path_over_to_path^-1 o path_to_transport o square_to_path.

  Global Instance path_over_map_isequiv
         {A B : Type} {f g : A -> B}
         {a₁ a₂ : A} {p : a₁ = a₂}
         {l : f a₁ = g a₁} {r : f a₂ = g a₂}
    : IsEquiv (@map_path_over A B f g a₁ a₂ p l r).
  Proof.
    unfold map_path_over.
    apply isequiv_compose.
  Defined.
End operations.