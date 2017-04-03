Require Import HoTT.

(* Path coequalizers as a higher inductive type *)
Module Export PathCoequalizer.

Variable A B : Type.
Variable p : A -> {b1 : B & {b2 : B & (b1 = b2) * (b1 = b2)}}.

Private Inductive pcoeq : Type :=
  inP : B -> pcoeq.

Definition left (x : A) : B := proj1_sig (p x).

Definition right (x : A) : B := proj1_sig (proj2_sig (p x)).

Definition first (x : A) : left x = right x := 
  fst(proj2_sig(proj2_sig (p x))).

Definition second (x : A) : left x = right x := 
  snd(proj2_sig(proj2_sig (p x))).

Axiom glueP : 
  forall (a : A), 
    ap inP (first a) = ap inP (second a).

(*
Lemma lem:coherency_compose in paper.
*)
Definition coherency (Y : pcoeq -> Type) (iY : forall (b : B), Y(inP b)) (a : A)
  : transport (fun b : B => Y (inP b)) (first a) (iY (left a)) 
  = transport (fun b : B => Y (inP b)) (second a) (iY (left a))
:=
    (transport_compose Y inP (first a) (iY (left a))
  @ (ap (fun p => transport Y p (iY (left a))) (glueP a))
  @ (transport_compose Y inP (second a) (iY (left a)))^).

(*
Induction rule for colimit using Licata's trick
*)
Fixpoint pcoeq_ind
  (Y : pcoeq -> Type)
  (iY : forall (b : B), Y(inP b))
  (gY : forall (a : A), (coherency Y iY a)^ @ (apD iY) (first a) = apD iY (second a))
  (x : pcoeq)
  {struct x}
  : Y x
  := (match x return _ -> Y x with
      | inP x => fun _ => iY x
    end) gY.
End PathCoequalizer.