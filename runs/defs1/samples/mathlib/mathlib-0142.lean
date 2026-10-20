@[expose] public section

variable {G α β ι : Type*}

open Filter

open scoped Topology NNReal

attribute [instance 10] NonUnitalSeminormedRing.toNonUnitalRing

/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class SeminormedRing (α : Type*) extends Norm α, Ring α, PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

end
