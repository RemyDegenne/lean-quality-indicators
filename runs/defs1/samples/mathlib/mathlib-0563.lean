public section

open Function

variable {G : Type*}

attribute [instance] IsAddCommutative.is_comm

attribute [instance] IsMulCommutative.is_comm

/-- A commutative multiplicative magma is a type with a multiplication which commutes. -/
@[ext]
class CommMagma (G : Type*) extends Mul G where
  /-- Multiplication is commutative in a commutative multiplicative magma. -/
  protected mul_comm : ∀ a b : G, a * b = b * a

end
