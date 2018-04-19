Module sma.

Variable D : Set.
Variable sum : D -> D -> D.
Variable product : D -> D -> D.
Infix "+" := sum.
Infix "*" := product.

(* Axiom closure : forall a, b : D => a + b \in D, a * b \in D *)
(* Axiom uniqueness_s : forall a, b : D, a = a', b = b' => a + b = a' + b'. *)
Axiom commutative_p : forall a : D, forall b : D, a + b = b + a.
Axiom commutative_m : forall a : D, forall b : D, a * b = b * a.

Axiom associative_p : forall a : D, forall b : D, forall c : D, a + (b + c) = (a + b) + c.
Axiom associative_m : forall a : D, forall b : D, forall c : D, a * (b * c) = (a * b) * c.

Axiom distributive : forall a : D, forall b : D, forall c : D, a * (b + c) = a * b + a * c.

Axiom zero : exists zero : D, forall a : D, a + zero = a.

Axiom unity : exists one : D, forall a : D, a * one = a.

(* Axiom additive_inv : forall a : D, exists a' : D, a + a' = zero. *)

(* Axiom cancellation : forall a : D, forall b : D, forall c : D, c != zero => c*a = c*b => a = b. *)

