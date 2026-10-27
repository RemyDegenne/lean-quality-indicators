@[expose] public section

namespace Complex

open scoped ComplexConjugate

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.re
  map_add' := add_re
  map_smul' := by simp

end Complex
end
