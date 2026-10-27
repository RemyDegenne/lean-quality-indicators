@[expose] public section

namespace NumberField

open Height

variable {K : Type*} [Field K] [NumberField K]

open AdmissibleAbsValues

/-- The absolute logarithmic height of an algebraic number. This is defined for elements of any
field of characteristic zero, with a junk value of `0` if the element is not algebraic. -/
noncomputable def absLogHeight₁ {K : Type*} [Field K] [CharZero K] (x : K) : ℝ :=
  (absMulHeight₁ x).log

end NumberField
end
