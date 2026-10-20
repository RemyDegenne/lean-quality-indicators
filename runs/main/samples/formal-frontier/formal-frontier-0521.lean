@[expose] public section

universe uK uΓ uL uΔ

open UniformSpace

open scoped Valued

namespace Valued

variable {K : Type uK} [Field K] {Γ₀ : Type uΓ}
  [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

section CompletionComparison

variable {L : Type uL} [Ring L] [Valued L Γ₀] [CompleteSpace L] [T0Space L]
  (f : K →+* L)
  (hValue : ∀ x, (v : Valuation L Γ₀) (f x) = (v : Valuation K Γ₀) x)
  (hDense : DenseRange f)

theorem uniformContinuous_completionRingEquiv_symm :
    UniformContinuous (completionRingEquiv f hValue hDense).symm := by
  exact uniformContinuous_of_denseRange_of_map_eq
    (completionRingEquiv f hValue hDense).symm.toRingHom.toAddMonoidHom
    (completionRingEquiv_symm_map_eq f hValue hDense)
    (completionRingEquiv f hValue hDense).symm.surjective.denseRange

end CompletionComparison
end Valued
end
