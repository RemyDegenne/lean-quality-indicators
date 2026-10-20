set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace CountableEndomorphism

universe u v

variable (S : Type u) (M : Type v) [Semiring S] [AddCommGroup M] [Module S M]

theorem rectangularRow_mul_rectangularColumn :
    rectangularRow S M * rectangularColumn S M = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, y₀_mul_x₀, y₁_mul_x₀,
      y₀_mul_x₁, y₁_mul_x₁]

end CountableEndomorphism
end
