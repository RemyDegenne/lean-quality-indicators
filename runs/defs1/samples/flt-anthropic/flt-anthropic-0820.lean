set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve.SymmetricPower

universe u

section Action

variable (k : Type u) [CommRing k] (r : ℕ)

@[reducible]
def permSMulCommClassMvPowerSeries :
    letI := permMulSemiringActionMvPowerSeries k r
    SMulCommClass (Equiv.Perm (Fin r)) k (MvPowerSeries (Fin r) k) := by
  letI := permMulSemiringActionMvPowerSeries k r
  refine ⟨fun σ c p => ?_⟩
  show MvPowerSeries.renameEquiv k σ (c • p) = c • MvPowerSeries.renameEquiv k σ p
  exact map_smul _ c p

end Action
end AlgebraicCurve.SymmetricPower
end
