public section

namespace TauCeti

open Complex Set

variable {U : Set ℂ} {f : ℂ → ℂ}

@[simp]
theorem _root_.DifferentiableOn.toOpenPartialHomeomorph_source
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) :
    (DifferentiableOn.toOpenPartialHomeomorph hf hU hinj).source = U :=
  (rfl)

end TauCeti
end
