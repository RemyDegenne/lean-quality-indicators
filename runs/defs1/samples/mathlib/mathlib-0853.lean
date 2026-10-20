@[expose] public section

open Set Function

@[inherit_doc] notation "ℂ" => Complex

namespace Complex

open scoped ComplexConjugate

attribute [local ext] Complex.ext

/-- The product of a set on the real axis and a set on the imaginary axis of the complex plane,
denoted by `s ×ℂ t`. -/
def reProdIm (s t : Set ℝ) : Set ℂ :=
  re ⁻¹' s ∩ im ⁻¹' t

end Complex
end
