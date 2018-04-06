Require Import HoTT.
Require Import polynomial.

Open Scope poly_scope.

(* The action of polynomials on maps preserves the identity. *)
Fixpoint poly_map_id (P : polynomial) {A : Type}
  : forall (x : poly_act P A), poly_map P idmap x = x
  := match P with
     | [-]     => fun x => idpath
     | const A => fun x => idpath
     | P * Q   => fun x => path_prod' (poly_map_id P (fst x)) (poly_map_id Q (snd x))
     | P + Q   => fun x =>
                    match x with
                    | inl y => ap inl (poly_map_id P y)
                    | inr y => ap inr (poly_map_id Q y)
                    end
     end.

(* The action of polynomials on maps preserves composition. *)
Fixpoint poly_map_compose
           (P : polynomial)
           {A B C : Type}
           (f : A -> B) (g : B -> C)
  : forall (x : poly_act P A), poly_map P (g o f) x = poly_map P g (poly_map P f x)
  := match P with
     | [-] => fun x => idpath
     | const A => fun x => idpath
     | P * Q => fun x => path_prod'
                           (poly_map_compose P f g (fst x))
                           (poly_map_compose Q f g (snd x))
     | P + Q => fun x =>
                  match x with
                  | inl y => ap inl (poly_map_compose P f g y)
                  | inr y => ap inr (poly_map_compose Q f g y)
                  end
     end.