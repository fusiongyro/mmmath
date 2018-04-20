Module sma.

Variable D : Set.
Variable sum : D -> D -> D.
Variable product : D -> D -> D.
Infix "+" := sum.
Infix "*" := product.
Axiom commutative_p : forall (a b : D), a + b = b + a.

(* Class IntegralDomain D : Type := {
 sum : D -> D -> D;
 product : D -> D -> D;
 Notation "x + y" := sum x y;
 Infix "+" := sum;
 Infix "*" := product;
}. *)

(* Axiom closure : forall a, b : D => a + b \in D, a * b \in D *)
(* Axiom uniqueness_s : forall a, b : D, a = a', b = b' => a + b = a' + b'. *)
Axiom commutative_m : forall a b : D, a * b = b * a.

Axiom associative_p : forall a b c : D, a + (b + c) = (a + b) + c.
Axiom associative_m : forall a b c : D, a * (b * c) = (a * b) * c.

Axiom distributive : forall a b c : D, a * (b + c) = a * b + a * c.

Axiom zero : exists zero : D, forall a : D, a + zero = a.

Axiom unity : exists one : D, forall a : D, a * one = a.
(* } *)
                         
Theorem abc : forall a : D, forall b : D, forall c : D,
        a + b + c = c + b + a.
Proof.
  intros.
  rewrite <- associative_p.
  replace (b + c) with (c + b).
  rewrite commutative_p.
  auto.
  rewrite commutative_p.
  auto.
Qed.  

(* Axiom additive_inv : forall a : D, exists a' : D, a + a' = zero. *)

(* Axiom cancellation : forall a : D, forall b : D, forall c : D, c != zero => c*a = c*b => a = b. *)

