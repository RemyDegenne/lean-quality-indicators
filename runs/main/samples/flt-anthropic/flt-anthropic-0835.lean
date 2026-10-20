namespace P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup OnePoint Function HahnSeries

open scoped MatrixGroups ModularForm Manifold

namespace X1DiamondLift

local notation "GL↑(" Γ ")" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Slash

variable {Γ Δ : Subgroup SL(2, ℤ)} {k : ℤ}

@[scoped simp] theorem coe_slashForm [Γ.FiniteIndex] [Normalizes Δ Γ] (γ : SL(2, ℤ)) (hγ : γ ∈ Δ)
    (f : ModularForm GL↑(Γ) k) :
    (⇑(slashForm γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) := rfl

end Slash
end X1DiamondLift
end
end P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar
