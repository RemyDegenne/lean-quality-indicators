public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial

open CFSG.Blueprint (NativeSporadic.Co1)

open CFSG.EvenSmallLie.OmegaEight (ind bNat qNat eichNat)

theorem conj_mem_R₀ {k : centralizer ({aNC} : Set NativeSporadic.Co1)} (hk : k ∈ K₀)
    {h : centralizer ({aNC} : Set NativeSporadic.Co1)} (hh : h ∈ R₀) : k * h * k⁻¹ ∈ R₀ :=
  ⟨mul_mem (mul_mem hk hh.1) (inv_mem hk), fun x hx => by
    rw [actV_mul (mul_mem hk hh.1), actV_mul hk, hh.2 _ (actV_mem (inv_mem hk) hx),
      ← actV_mul hk, mul_inv_cancel, actV_one hx]⟩

end CFSG.Sporadic.Co1Patterson.TwistNative
end
