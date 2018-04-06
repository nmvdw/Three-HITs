Require Import HoTT.

(** We look at heterogeneous equality.
    This is equality between inhabitants of different types.
    We follow the paper 'Cubical Methods in SYnthetic Homotopy Theory.
 *)

(** The first definition is via an inductive tyoe. *)
Inductive heq : forall {A B : Type} (p : A = B) (a : A) (b : B), Type :=
| heq_refl : forall {A : Type} (a : A), heq idpath a a.

(** The second definition uses path induction *)
Definition heq_pi {A B : Type} (p : A = B)
  : A -> B -> Type
  := match p with
     | idpath => fun a b => a = b
     end.

Section equivalences.
  (** Heterogenous equality can be understood as a homogeneous equality.
      For that we need to coerce along the type equality.
      This gives an equivalent definition.
   *)
  Definition heq_to_path_coe
             {A B : Type}
             {p : A = B}
             {a : A} {b : B}
             (q : heq p a b)
    : transport idmap p a = b
    := match q with
       | heq_refl _ _ => idpath
       end.

  Definition path_coe_to_heq
             {A B : Type}
             {p : A = B}
    : forall {a : A} {b : B} (q : transport idmap p a = b), heq p a b
    := match p with
       | idpath => fun a b q => transport (heq 1 a) q (heq_refl a)
       end.

  Global Instance heq_to_path_coeq
         {A B : Type}
         {p : A = B}
         {a : A} {b : B}
    : IsEquiv (@heq_to_path_coe A B p a b).
  Proof.
    simple refine (isequiv_adjointify _ (@path_coe_to_heq A B p a b) _ _).
    - intros x.
      induction p, x ; reflexivity.
    - intros x.
      induction x ; reflexivity.
  Defined.

  (** Alternatively, we can coerce along the inverse of the type equality.
      This gives an equivalent definition as well.
   *)
  Definition heq_to_path_coe_V
             {A B : Type}
             {p : A = B}
             {a : A} {b : B}
             (q : heq p a b)
    : a = transport idmap p^ b
    := match q with
       | heq_refl _ _ => idpath
       end.

  Definition path_coe_V_to_heq
             {A B : Type}
             {p : A = B}
    : forall {a : A} {b : B} (q : a = transport idmap p^ b), heq p a b
    := match p with
       | idpath => fun a b q => transport (heq 1 a) q (heq_refl a)
       end.

  Global Instance heq_to_path_coeq_V
         {A B : Type}
         {p : A = B}
         {a : A} {b : B}
    : IsEquiv (@heq_to_path_coe_V A B p a b).
  Proof.
    simple refine (isequiv_adjointify _ (@path_coe_V_to_heq A B p a b) _ _).
    - intros x.
      induction p ; cbn in x ; induction x.
      reflexivity.
    - intros x.
      induction x ; reflexivity.
  Defined.

  (** Lastly, the two definitions of heterogeneous equality given in the beginning, are equivalent.
   *)
  Definition heq_to_heq_pi
             {A B : Type}
             {p : A = B}
             {a : A} {b : B}
             (q : heq p a b)
    : heq_pi p a b
    := match q with
       | heq_refl _ _ => idpath
       end.

  Definition heq_pi_to_heq
             {A B : Type}
             {p : A = B}
    : forall {a : A} {b : B} (q : heq_pi p a b), heq p a b
    := match p with
       | idpath => fun a b q => transport (heq idpath a) q (heq_refl _)
       end.

  Global Instance heq_to_heq_pi_is_equiv
             {A B : Type}
             {p : A = B}
             {a : A} {b : B}
    : IsEquiv (@heq_to_heq_pi A B p a b).
  Proof.
    simple refine (isequiv_adjointify _ (@heq_pi_to_heq A B p a b) _ _).
    - intros x.
      induction p, x.
      reflexivity.
    - intros x.
      induction x.
      reflexivity.
  Defined.
End equivalences.