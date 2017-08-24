Require Import HoTT.
Require Import HoTT.HIT.Colimits.

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

(* In order to nicely work with colimits over the natural numbers, we want to abbreviate some principles.
   These principles are closer to what was written in the paper, and follow from the more general rules.
 *)

(* Colimits as coequalizers of sums.
   Again we do it for arbitrary diagrams.
*)
Section ColimAsCoeq.

  Variable (G : graph) (D : diagram G).

  Definition C1 := sigT (diagram0 D).
  Definition B := sigT (fun i : G => D i * sigT (fun j : G => G i j)).

  Definition g1 (x : B) : C1 :=
    match x with
    | (i;(x,_)) => (i;x)
    end.

  Definition g2 (x : B) : C1 :=
    match x with
    | (_;(x,(j;g))) => (j;diagram1 D g x)
    end.

  Definition C : Type := Coeq g1 g2.
  Definition H : Type := colimit D.

  Definition CToH : C -> H.
  Proof.
    simple refine (Coeq_rec _ _ _).
    - intros [x z].
      apply (colim x z).
    - intros [i [x [j g]]].
      apply (colimp i j g x)^.
  Defined.

  Definition HToC : H -> C.
  Proof.
    simple refine (colimit_rec _ _).
    simple refine (Build_cocone _ _).
    - intros i x.
      apply (coeq(i;x)).
    - intros i j g x.
      apply (@cp B C1 g1 g2 (i;(x,(j;g))))^.
  Defined.

  Global Instance CToH_equiv : IsEquiv CToH.
  Proof.
    apply isequiv_biinv.
    split ; refine (HToC;_).
    - simple refine (Coeq_ind _ _ _).
      * intros.
        reflexivity.
      * intros [i [x [j g]]].
        rewrite transport_paths_FlFr.
        rewrite ap_idmap.
        rewrite ap_compose.
        rewrite concat_p1.
        rewrite Coeq_rec_beta_cp.
        rewrite ap_V.
        rewrite inv_V.
        rewrite colimit_rec_beta_colimp.
        hott_simpl.
    - simple refine (colimit_ind _ _ _).
      * intros.
        reflexivity.
      * intros.
        rewrite transport_paths_FlFr.
        rewrite ap_idmap.
        rewrite ap_compose.
        rewrite concat_p1.
        rewrite colimit_rec_beta_colimp.
        simpl.
        rewrite ap_V.
        rewrite Coeq_rec_beta_cp.
        hott_simpl.
  Defined.

End ColimAsCoeq.

(*
The colimit of F(X) = A is A.
Lemma 10 in paper.
*)
Section ColimConst.

  Variable A : Type.
  
  Definition ConstantD : diagram mappingtelescope_graph :=
    Build_sequence (fun _ => A) (fun _ => idmap).

  Definition Constant := colimit ConstantD.

  (* colim A id -> A
     Defined by F(n) -> A as id.
   *)
  Definition ConstantToA :
    Constant -> A.
  Proof.
    simple refine (colimit_rec A (Build_cocone _ _)).
    - apply (fun _ => idmap).
    - intros i j [ ] x.
      reflexivity.
  Defined.

  Definition AToConstant (a : A) : Constant.
  Proof.
    simple refine (colim _ _).
    - apply 0.
    - apply a.
  Defined.

  Definition AToConstantToA (x : A) :
    ConstantToA (AToConstant x) = x := idpath.

  Definition ConstantToAToConstant :
    forall (x : Constant), AToConstant (ConstantToA x) = x.
  Proof.
    simple refine (colimit_ind _ _ _).
    - intros n x.
      induction n.
      * reflexivity.
      * apply
          (  IHn _
               @
               (@colimp mappingtelescope_graph ConstantD n (n.+1) idpath x)^
          ).
    - intros.
      destruct g.
      refine (transport_paths_FlFr (@colimp mappingtelescope_graph ConstantD i _ _ x) _ @ _).
      refine (ap (fun p => _ @ p) (ap_idmap (colimp _ _ _ _)) @ _).
      refine (ap (fun q => ((q^ @ _) @ _)) (ap_compose ConstantToA _ (colimp _ _ _ _)) @ _).
      refine (ap (fun p => ((ap _ p)^ @ _) @ _) (colimit_rec_beta_colimp _ _ _ _ _ _) @ _).  
      hott_simpl.
  Defined.

  Global Instance ConstantToA_equiv : IsEquiv ConstantToA.
  Proof.
    apply isequiv_biinv.
    split ; exists AToConstant ; intro x.
    - apply ConstantToAToConstant.
    - apply AToConstantToA.
  Defined.

End ColimConst.

(* The colimit of the sum of two diagrams is the sum of the colimit of the diagrams.
   We show this for arbitrary diagrams.
*)
Section ColimSum.

  Variable (G : graph)
           (D1 D2 : diagram G).

  (* The sum diagram *)

  Definition SumD : diagram G :=
    Build_diagram
      G
      (fun x => diagram0 D1 x + diagram0 D2 x)
      (fun i j g x =>
         match x with
         | inl y => inl (diagram1 D1 g y)
         | inr z => inr (diagram1 D2 g z)
         end
      ).
  
  Definition ColimitSum := colimit SumD.
  Definition Sum := colimit D1 + colimit D2.

  Definition ColimToSum : ColimitSum -> Sum.
  Proof.
    simple refine (colimit_rec _ _).
    simple refine (Build_cocone _ _).
    - intros i [y | z].
      * apply (inl (colim i y)).
      * apply (inr (colim i z)).
    - intros i j g [d | d].
      * apply (ap inl (colimp i j g d)).
      * apply (ap inr (colimp i j g d)).
  Defined.

  Definition SumToColim (x : Sum) : ColimitSum.
  Proof.
    destruct x as [y | z].
    - simple refine (colimit_rec _ _ y).
      simple refine (Build_cocone _ _).
      * intros.
        apply (colim i).
        simple refine (@inl _ _ X).
      * intros.
        apply (colimp i j g (inl x : SumD i)).
    - simple refine (colimit_rec _ _ z).
      simple refine (Build_cocone _ _).
      * intros.
        apply (colim i).
        simple refine (@inr _ _ X).
      * intros.
        apply (colimp i j g (inr x : SumD i)).
  Defined.

  Lemma SumToColimToSum : forall x : Sum,
      ColimToSum(SumToColim x) = x.
  Proof.
    destruct x as [y | y].
    - simple refine
             (@colimit_ind _ _
               (fun x : colimit D1 => ColimToSum (SumToColim (inl x)) = inl x) _ _ _
             ).
      * apply (fun _ _ => idpath).
      * intros.
        rewrite transport_paths_FlFr.
        rewrite ap_compose.
        rewrite colimit_rec_beta_colimp.
        rewrite concat_p1.
        pose (z := inl x : SumD i).
        assert (ap ColimToSum (colimp i j g z) = ap inl (colimp i j g x)).
        apply colimit_rec_beta_colimp.

        rewrite X.
        apply concat_Vp.
    - simple refine (@colimit_ind G D2 (fun x : colimit D2 => ColimToSum (SumToColim (inr x)) = inr x) _ _ _).
      * reflexivity.
      * cbn.
        intros.
        rewrite transport_paths_FlFr.
        rewrite ap_compose.
        rewrite concat_p1.
        rewrite colimit_rec_beta_colimp.
        pose (z := inr x : SumD i).
        assert (ap ColimToSum (colimp i j g z) = ap inr (colimp i j g x)).
        apply colimit_rec_beta_colimp.

        rewrite X.
        apply concat_Vp.
  Qed.

  Theorem ColimToSumToColim : forall x : ColimitSum,
      SumToColim(ColimToSum x) = x.
  Proof.
    simple refine (colimit_ind _ _ _); cbn.
    - intros.
      destruct x as [y| z]; reflexivity.
    - intros.
      etransitivity.
      {
        simple refine (transport_paths_FlFr (colimp _ _ _ _) _).
      }
      etransitivity.
      {
        simple refine (ap (fun p => _ @ p) (ap_idmap _)).
      }
      etransitivity.
      {
        simple refine (ap (fun p => (p^ @ _) @ _) (ap_compose ColimToSum SumToColim (colimp _ _ _ _))).
      }  
      destruct x as [y | y]; rewrite concat_p1.
      * pose (z := inl y : SumD i).
        assert (ap ColimToSum (colimp i j g z) = ap inl (colimp i j g y)).
        apply colimit_rec_beta_colimp.

        rewrite X.
        rewrite <- (ap_compose inl).
        cbn.
        rewrite colimit_rec_beta_colimp.
        cbn.
        hott_simpl.
      * pose (z := inr y : SumD i).
        assert (ap ColimToSum (colimp i j g z) = ap inr (colimp i j g y)).
        apply colimit_rec_beta_colimp.

        rewrite X.
        rewrite <- (ap_compose inr).
        cbn.
        rewrite colimit_rec_beta_colimp.
        hott_simpl.
  Qed.

  Theorem BiInv_ColimToSum : BiInv ColimToSum.
  Proof.
    split.
    - exists SumToColim.
      unfold Sect.
      apply ColimToSumToColim.
    - exists SumToColim.
      unfold Sect.
      apply SumToColimToSum.
  Qed.

  Theorem Equiv_ColimToSum : IsEquiv ColimToSum.
  Proof.
    apply isequiv_biinv.
    apply BiInv_ColimToSum.
  Qed.
End ColimSum.

Definition colim_N (F : nat -> Type) (f : forall n : nat, F n -> F(S n)) : Type :=
  colimit (Build_sequence F f).

Definition inc (F : nat -> Type) (f : forall n : nat, F n -> F(S n)) (n : nat) (x : F n) : colim_N F f
  := @colim mappingtelescope_graph (Build_sequence F f) n x.

Definition com (F : nat -> Type) (f : forall n : nat, F n -> F(S n)) (n : nat) (x : F n) :
  inc F f (S n) (f n x) = inc F f n x.
Proof.
compute.
pose (@colimp mappingtelescope_graph (Build_sequence F f) n (S n) (reflexivity (S n)) x).
compute in p.
eapply p.
Defined.

Definition cocone_P 
  (P : Type)
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (Pi : forall (n : nat), F n -> P)
  (Pc : forall (n : nat) (x : F n), Pi (S n) (f n x) = Pi n x)
  : cocone (Build_sequence F f) P.
Proof.
simple refine (Build_cocone _ _).
- eapply Pi.

- cbn.
  intros.
  induction g.
  eapply Pc.
Defined.

Definition colim_N_rec
  (P : Type)
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (Pi : forall (n : nat), F n -> P)
  (Pc : forall (n : nat) (x : F n), Pi (S n) (f n x) = Pi n x) :
  colim_N F f -> P
  := @colimit_rec mappingtelescope_graph (Build_sequence F f) P (cocone_P P F f Pi Pc).

Definition colim_N_rec_beta_com
  (P : Type)
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (Pi : forall (n : nat), F n -> P)
  (Pc : forall (n : nat) (x : F n), Pi (S n) (f n x) = Pi n x)
  (n : nat)
  (x : F n) :
  ap (colim_N_rec P F f Pi Pc) (com F f n x) = Pc n x.
Proof.
assert
 (ap
    (@colimit_rec mappingtelescope_graph (Build_sequence F f) P
       (cocone_P P F f Pi Pc))
    (@colimp mappingtelescope_graph (Build_sequence F f) n n.+1
       (reflexivity n.+1) x) =
  qq (cocone_P P F f Pi Pc) n n.+1 (reflexivity n.+1) x).
- apply (colimit_rec_beta_colimp P (cocone_P P F f Pi Pc) n 
     (S n) (reflexivity (S n)) x).

- cbn in X.
  apply X.
Defined.

Definition colim_N_ind
  (F : nat -> Type)
  (f : forall (n : nat), F n -> F(S n))
  (P : colim_N F f -> Type)
  (Pi : forall (n : nat), forall (x : F n), P (inc F f n x))
  (Pc : forall (n : nat) (x : F n), (com F f n x) # Pi (S n) (f n x) = Pi n x) :
  forall (x : colim_N F f), P x.
Proof.
simple refine (colimit_ind _ _ _) ; cbn.
- apply Pi.
- intros.
  induction g.
  apply Pc.
Defined.

Module ColimProd.

Parameter F G : nat -> Type.
Parameter f : forall n, F n -> F(S n).
Parameter g : forall n, G n -> G(S n).
(*
Definition colimProd := prod (colim_N F f) (colim_N G g).

Definition DiagObj (i : nat) : Type := prod (F i) (G i).
Definition DiagMap (i : nat) (x : DiagObj i) :=
  match x with
  | pair fst snd => pair (f i fst) (g i snd)
  end.
Definition colimDiag : Type := colim_N DiagObj DiagMap.

Definition HObj (i : nat) : Type := prod (F i) (colim_N G g).
Definition HMap (i : nat) (x : HObj i) : HObj (S i).
Proof.
destruct x.
apply (pair (f i fst) snd).
Defined.

Definition TotObj (i j : nat) := prod (F i) (G j).
Definition TotMap (i j : nat) (x : TotObj i j) : TotObj i (S j).
Proof.
destruct x.
apply (pair fst (g j snd)). 
Defined.
Definition column (i : nat) := colim_N (TotObj i) (TotMap i).

Definition columnMap (i : nat) : column i -> column (S i).
Proof.
simple refine (colim_N_rec (column (S i)) (TotObj i) (TotMap i) _ _).
- intros j [x y].
  simple refine (inc _ _ j (pair (f i x) y)).
- intros j [x y]. 
  apply (com (TotObj i.+1) (TotMap i.+1) j (pair (f i x) y)).
Defined.  

Definition colimTot := colim_N column columnMap.

Lemma kek (i : nat) : column i -> HObj i.
Proof.
  

(*
Follows from is_colimit_prod
colim_i colim_j (F i * G j) = colim_i (F i * (colim_j G j)) 
*)
Theorem TotToH : colimTot -> colimH.
Proof.
  admit.
Admitted.

(*
Follows from is_colimit_prod
colim_i (F i * colim_j G j) = colim_i (F i) * colim_j (G j)
*)
Theorem HToProd : colimH -> product.
Proof.
  admit.
Admitted.

Theorem DiagToTot : colimDiag -> colimTot.
Proof.
simple refine (colim_N_rec _ _ _ _ _).
- intros i [x y].
  simple refine (inc _ _ i _).
  cbn.
  simple refine (inc _ _ i (pair x y)).
- intros n [x y].
  compute.
  admit.
Admitted.

Theorem TotToDiag : colimTot -> colimDiag.
Proof.
simple refine (colim_N_rec _ _ _ _ _) ; cbn.  
- intro n.
  simple refine (colim_N_rec _ _ _ _ _).
  *  intros m [x y].
     simple refine (inc _ _ (max n m) _).
     cbn.
     admit.
Admitted.
*)
End ColimProd.