(* This files is for general facts used in the paper *)

Require Import HoTT.
Require Export HoTT.

(*
Lemma lem:pathext
*)
Definition apTransport (A B : Type) (f g : A -> B) (e : f = g) (x y : A) (p : x = y) :
  transport (fun h => h x = h y) e (ap f p) = ap g p :=
match e with
  idpath => 1
end.

(*
Definition def:ap_ext_pt.
 *)
Definition fPath `{Funext} {A B : Type} {f g : A -> B} (e : f = g) (x : A) : f x = g x
  := (path_forall f g)^-1 e x.

Definition fPath_point `{Funext} {A B : Type} {f g : A -> B} (e : f == g) (x : A)
  : fPath (path_forall _ _ e) x = e x := apD10_path_arrow _ _ _ _.

(*
Lemma lem:funTrans
*)
Definition funTransport `{Funext} (A B : Type) (f g : A -> B) (e : f = g) (x y : A) (p : f x = f y) :
  transport (fun h => h x = h y) e p = (fPath e x)^ @ p @ (fPath e y) :=
match e with
  idpath => (concat_p1 p)^ @ (ap (fun q => q @ 1) (concat_1p p))^
end.

Definition apd2
 (A : Type) (Y : A -> Type) (f : forall x : A, Y x) (a b : A) (p q : a = b) (s : p = q) :
  transport (fun r : a = b => r # f a = f b) s (apD f p) = apD f q :=
match p with
| refl => apD (fun r => apD f r) s
end.
