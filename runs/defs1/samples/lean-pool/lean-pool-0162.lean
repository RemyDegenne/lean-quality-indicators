@[expose] public section

open scoped TensorProduct nonZeroDivisors

namespace BGS.HasseWeil

noncomputable section

section TensorFraction

variable (K E A : Type*) [Field K] [Field E] [CommRing A]
  [Algebra K E] [Algebra K A]

/-- Tensor the fraction field of `A` with an extension field `E / K`. -/
abbrev TensorFraction := E ⊗[K] FractionRing A

end TensorFraction
end
end BGS.HasseWeil
end
