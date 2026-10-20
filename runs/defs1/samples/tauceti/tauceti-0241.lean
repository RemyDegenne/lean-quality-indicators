public section

namespace TauCeti

open scoped nonZeroDivisors NumberField ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-- The finite set of nonzero integral ideals with a fixed absolute norm. -/
noncomputable def normFiber (n : ℕ) : Finset ((Ideal (𝓞 K))⁰) :=
  (finite_normFiber K n).toFinset

end TauCeti
end
