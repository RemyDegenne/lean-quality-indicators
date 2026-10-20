public section

open scoped DirectSum

namespace TauCeti

open LaurentPolynomial

universe u v v'

variable (k : Type u) [DivisionRing k]

variable (V : ℤ → Type v) [∀ j, AddCommGroup (V j)] [∀ j, Module k (V j)]

variable {k V}

theorem targetShiftGradedDimension_shortExact
    {U : ℤ → Type v'} [∀ j, AddCommGroup (U j)] [∀ j, Module k (U j)]
    {W : ℤ → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (hU : HasFiniteLaurentSupport k U) (hW : HasFiniteLaurentSupport k W)
    (f : ∀ j, U j →ₗ[k] V j) (g : ∀ j, V j →ₗ[k] W j)
    (hinj : ∀ j, Function.Injective (f j)) (hfg : ∀ j, Function.Exact (f j) (g j))
    (hsurj : ∀ j, Function.Surjective (g j)) :
    targetShiftGradedDimension k V (HasFiniteLaurentSupport.of_exact hU hW f g hfg) =
      targetShiftGradedDimension k U hU + targetShiftGradedDimension k W hW := by
  simp only [targetShiftGradedDimension]
  rw [gradedDimension_shortExact hU hW f g hinj hfg hsurj, map_add]

end TauCeti
end
