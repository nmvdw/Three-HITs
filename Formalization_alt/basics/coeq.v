Require Import HoTT.

Definition coeq_fmap
           {A₁ B₁ A₂ B₂ : Type}
           (f₁ g₁ : A₁ -> B₁)
           (f₂ g₂ : A₂ -> B₂)
           (h₁ : A₁ -> A₂)
           (h₂ : B₁ -> B₂)
           (c₁ : f₂ o h₁ == h₂ o f₁)
           (c₂ : g₂ o h₁ == h₂ o g₁)
  : Coeq f₁ g₁ -> Coeq f₂ g₂
  := Coeq_rec (Coeq f₂ g₂)
              (coeq o h₂)
              (fun a => ap coeq (c₁ a)^ @ cp (h₁ a) @ ap coeq (c₂ a)).

Definition coeq_fmap_id
           {A B : Type}
           (f g : A -> B)
           `{Funext}
  : coeq_fmap f g f g idmap idmap (fun _ => idpath) (fun _ => idpath)
    =
    idmap.
Proof.
  funext x ; revert x.
  simple refine (Coeq_ind _ (fun _ => idpath) _).
  intros a ; cbn.
  rewrite transport_paths_FlFr, ap_idmap, concat_p1.
  unfold coeq_fmap.
  rewrite Coeq_rec_beta_cp, concat_1p, concat_p1.
  apply concat_Vp.
Defined.

Definition coeq_fmap_compose
           {A₁ B₁ A₂ B₂ A₃ B₃ : Type}
           (f₁ g₁ : A₁ -> B₁)
           (f₂ g₂ : A₂ -> B₂)
           (f₃ g₃ : A₃ -> B₃)
           (h₁ : A₁ -> A₂)
           (h₂ : B₁ -> B₂)
           (ϕ₁ : A₂ -> A₃)
           (ϕ₂ : B₂ -> B₃)
           (c₁ : f₂ o h₁ == h₂ o f₁)
           (c₂ : g₂ o h₁ == h₂ o g₁)
           (d₁ : f₃ o ϕ₁ == ϕ₂ o f₂)
           (d₂ : g₃ o ϕ₁ == ϕ₂ o g₂)
  : Type.
Proof.
  simple refine (
  coeq_fmap f₁ g₁ f₃ g₃ (ϕ₁ o h₁) (ϕ₂ o h₂) _ _
    =
    (coeq_fmap f₂ g₂ f₃ g₃ ϕ₁ ϕ₂ d₁ d₂)
      o
      (coeq_fmap f₁ g₁ f₂ g₂ h₁ h₂ c₁ c₂)
         ).
Admitted.