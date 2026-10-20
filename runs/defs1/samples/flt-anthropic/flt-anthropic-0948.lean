namespace P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup OnePoint Function HahnSeries

open scoped MatrixGroups ModularForm Manifold

namespace X1DiamondLift

local notation "GL↑(" Γ ")" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Stretch

variable {Γ Γ' Δ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {ℓ : ℕ} {k : ℤ}

variable (hΓ' : ∀ γ ∈ Γ', ∃ γ₁ ∈ Γ,
  γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1)

def expandPS (ℓ : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0

end Stretch
end X1DiamondLift
end
end P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar
