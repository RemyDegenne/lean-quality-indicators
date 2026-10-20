public section

noncomputable section

namespace TauCeti

open scoped ContDiff

universe u

section IteratedGradientChain

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The classical derivative fields of a scalar function, in the basis-free nested-linear-map
types `TauCeti.IteratedGradient`. Index zero is the gradient and each successor is the Fréchet
derivative of the preceding field. -/
noncomputable def iteratedGradientChain (f : F → ℝ) :
    (j : ℕ) → F → IteratedGradient F j
  | 0 => fun x => gradient f x
  | j + 1 => fderiv ℝ (iteratedGradientChain f j)

end IteratedGradientChain
end TauCeti
end
end
