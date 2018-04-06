Require Import HoTT.

Class functor (F : Type -> Type) :=
  { fmap : forall {X Y : Type} (f : X -> Y), F X -> F Y ;
    fmap_id : forall {X : Type}, fmap (idmap : X -> X) = idmap ;
    fmap_compose : forall {X Y Z : Type} (f : X -> Y) (g : Y -> Z),
        fmap (g o f) = fmap g o fmap f
  }.

Arguments fmap F {_ X Y} f _.
Arguments fmap_id {F _ X}.
Arguments fmap_compose {F _ X Y Z} f g.

Notation "F $ f" := (fmap F f) (at level 30).

Section functor_on_point.
  Variable (F : Type -> Type).
  Context `{functor F}.

  Definition fmap_id_point {X : Type}
    : F $ (idmap : X -> X) == idmap
    := fun z => ap (fun f => f z) fmap_id.

  Definition fmap__point {X Y Z : Type} (f : X -> Y) (g : Y -> Z)
    : F $ (g o f) == F $ g o F $ f
    := fun z => ap (fun f => f z) (fmap_compose f g).
End functor_on_point.

Global Instance functor_idmap : functor idmap
  := {|
      fmap := fun _ _ => idmap ;
      fmap_id := fun _ => idpath ;
      fmap_compose := fun _ _ _ _ _ => idpath
    |}.
