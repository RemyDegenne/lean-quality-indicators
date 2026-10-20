namespace P2MW.S_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup OnePoint Function HahnSeries ModularCurve

open scoped MatrixGroups ModularForm Manifold

namespace X1DiamondGalois

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Slash

variable {M : ℕ} {k : ℤ}

theorem diamondSlash_ne_zero [NeZero M] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M)
    {f : ModularForm Γ₁(M) k} (hf : f ≠ 0) : diamondSlash γ hγ f ≠ 0 := by
  intro h
  apply hf
  have h1 : (⇑(diamondSlash γ hγ f) : ℍ → ℂ) = 0 := by rw [h]; rfl
  rw [coe_diamondSlash_SL] at h1
  have h2 : (⇑f : ℍ → ℂ) = 0 := by
    rw [← slash_slash_inv (k := k) (⇑f) γ, h1, SlashAction.zero_slash]
  exact DFunLike.ext' (h2.trans ModularForm.coe_zero.symm)

end Slash
end X1DiamondGalois
end
end P2MW.S_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff
