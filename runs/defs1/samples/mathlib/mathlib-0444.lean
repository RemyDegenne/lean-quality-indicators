@[expose] public section

universe u v w w₁ w₂

section OfAssociative

variable {A : Type v} [Ring A]

namespace LieRing

/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
@[instance_reducible]
def ofAssociativeRing : LieRing A where
  add_lie _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_add _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_self := by simp only [Ring.lie_def, forall_const, sub_self]
  leibniz_lie _ _ _ := by
    simp only [Ring.lie_def, mul_sub_left_distrib, mul_sub_right_distrib, mul_assoc]; abel

end LieRing
end OfAssociative
end
