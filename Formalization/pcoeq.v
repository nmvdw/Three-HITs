Require Import HoTT.

Definition coherency
           {B C : Type}
           (Y : C -> Type)
           (g : B -> C)
           {b1 b2 : B}
           (p q : b1 = b2)
           (h : ap g p = ap g q)
           (x : Y(g b1))
  : transport (fun b : B => Y (g b)) p x 
    = transport (fun b : B => Y (g b)) q x
  := (transport_compose Y g p x)
       @ (ap (fun p => transport Y p x) h)
       @ (transport_compose Y g q x)^.

Definition ap_eq_fun
           {A B : Type}
           (f g : A -> B)
           {a b : A}
           (e : forall x, f x = g x)
           (p : a = b)
  : ap f p = (e a) @ ap g p @ (e b)^.
Proof.
  induction p.
  apply (ap (fun p => p @ _) (concat_p1 _) @ concat_pV _)^.
Defined.

(* Path coequalizers as a higher inductive type *)
Module Export PathCoequalizer.

  Section PathCoeq.
    Private Inductive pcoeq
            {A B : Type}
            (p : A -> {b1 : B & {b2 : B & (b1 = b2) * (b1 = b2)}})
    : Type
      :=
      | inP : B -> pcoeq p.

    Variable (A B : Type)
             (p : A -> {b1 : B & {b2 : B & (b1 = b2) * (b1 = b2)}}).
    
    Definition end_l (x : A) : B := (p x).1.
    Definition end_r (x : A) : B := (p x).2.1.
    Definition path_l (x : A) : end_l x = end_r x := fst((p x).2.2).
    Definition path_r (x : A) : end_l x = end_r x := snd((p x).2.2).

    Axiom glueP : 
      forall (a : A), 
        ap (inP p) (path_l a) = ap (inP p) (path_r a).

  End PathCoeq.

  Arguments glueP {_} {_} _ _.
  Arguments end_l {_} {_} _ _.
  Arguments end_r {_} {_} _ _.
  Arguments path_l {_} {_} _ _.
  Arguments path_r {_} {_} _ _.

  Section PathCoeqInd.
    Variable (A B : Type)
             (p : A -> {b1 : B & {b2 : B & (b1 = b2) * (b1 = b2)}})
             (Y : pcoeq p -> Type)
             (iY : forall (b : B), Y(inP p b)).

    (*
    Induction rule for colimit using Licata's trick
     *)
    Fixpoint pcoeq_ind
             (gY : forall (a : A),
                 (coherency Y (inP p) _ _ (glueP p a) _)^
                 @ apD iY (path_l p a)
                 = apD iY (path_r p a))
             (x : pcoeq p)
      : Y x
      := (match x return _ -> Y x with
          | inP x => fun _ => iY x
          end) gY.
  End PathCoeqInd.
End PathCoequalizer.