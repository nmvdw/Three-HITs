Require Import HoTT.

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
    
    Definition left (x : A) : B := (p x).1.

    Definition right (x : A) : B := (p x).2.1.

    Definition first (x : A) : left x = right x := fst((p x).2.2).

    Definition second (x : A) : left x = right x := snd((p x).2.2).

    Axiom glueP : 
      forall (a : A), 
        ap (inP p) (first a) = ap (inP p) (second a).

  End PathCoeq.

  Arguments glueP {_} {_} _ _.
  Arguments left {_} {_} {_} _.
  Arguments right {_} {_} {_} _.
  Arguments first {_} {_} {_} _.
  Arguments second {_} {_} {_} _.

  Section PathCoeqInd.
    Variable (A B : Type)
             (p : A -> {b1 : B & {b2 : B & (b1 = b2) * (b1 = b2)}})
             (Y : pcoeq p -> Type)
             (iY : forall (b : B), Y(inP p b)).

    (*
    Lemma lem:coherency_compose in paper.
    *)
    Definition coherency (a : A)
      : transport (fun b : B => Y (inP p b)) (first a) (iY (left a)) 
        = transport (fun b : B => Y (inP p b)) (second a) (iY (left a))
      :=
        (transport_compose Y (inP p) (first a) (iY (left a))
                           @ (ap (fun p => transport Y p (iY (left a))) (glueP p a))
                           @ (transport_compose Y (inP p) (second a) (iY (left a)))^).

    (*
    Induction rule for colimit using Licata's trick
     *)
    Fixpoint pcoeq_ind
             (gY : forall (a : A), (coherency a)^ @ (apD iY) (first a) = apD iY (second a))
             (x : pcoeq p)
      : Y x
      := (match x return _ -> Y x with
          | inP x => fun _ => iY x
          end) gY.
  End PathCoeqInd.
  
End PathCoequalizer.