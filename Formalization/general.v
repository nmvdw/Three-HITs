(* This files is for general facts used in the paper *)

Require Import HoTT.
Require Export HoTT.
Require Import FunextAxiom.

(*
Lemma lem:pathext
*)
Definition apTransport (A B : Type0) (f g : A -> B) (e : f = g) (x y : A) (p : x = y) :
  transport (fun h => h x = h y) e (ap f p) = ap g p :=
match e with
  idpath => 1
end.

(*
Definition def:ap_ext_pt.
*)
Definition fPath {A B : Type0} {f g : A -> B} (e : f = g) (x : A) : f x = g x :=
match e with
  idpath => 1
end.

(*
Lemma lem:funTrans
*)
Definition funTransport (A B : Type0) (f g : A -> B) (e : f = g) (x y : A) (p : f x = f y) :
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
