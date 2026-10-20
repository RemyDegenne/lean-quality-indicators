namespace P2MW.S_MvFormalGroup_mem_firstOrderCoboundaries_iff

attribute [-instance] MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing

set_option autoImplicit false

noncomputable section

open MvPowerSeries MvFormalGroup

namespace K4Aux

variable {k : Type} [Field k]

local notation "K" => DualNumber k

variable {σ : Type}

section Bf

variable {d : ℕ} (G₀ : MvFormalGroup d k)

theorem bf_smul (c : k) (η : Fin d → MvPowerSeries (Fin d) k) (l : Fin d) : bf G₀ (c • η) l = c • bf G₀ η l := by
  simp only [bf, Pi.smul_apply, MvPowerSeries.subst_smul (hasSubst_Xl (k := k) (d := d)), MvPowerSeries.subst_smul (hasSubst_Xr (k := k) (d := d)),
    MvPowerSeries.subst_smul G₀.hasSubst_toPowerSeries, smul_mul_assoc, smul_add, smul_sub, Finset.smul_sum]

end Bf
end K4Aux
end
end P2MW.S_MvFormalGroup_mem_firstOrderCoboundaries_iff
