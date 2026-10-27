public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35U

open Subgroup Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.LocalAnalysis.GorensteinLyons.FourUnitary

open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem exists_smul_eq_of_mem_centralizer (hm : 3 ≤ m) {e : Fin m → K} (he0 : e ≠ 0)
    (he : herm frob e e = 0) {g : SUid frob m}
    (hg : (QuotientGroup.mk g : PG m) ∈ centralizer {tq e}) :
    ∃ μ : K, μ ≠ 0 ∧ g • e = μ • e := by
  have h1 : tq (g • e) = tq e := by
    rw [← conj_tq g he, mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have hge0 : g • e ≠ 0 := (smul_ne_zero_iff_ne g).mpr he0
  have hge : herm frob (g • e) (g • e) = 0 := by rw [herm_smul_smul, he]
  obtain ⟨c, hc⟩ := (tq_eq_tq_iff hm hge0 hge he0 he).mp h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact he0 hc
  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
  calc g • e = c⁻¹ • (c • (g • e)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • e := by rw [← hc]

end CFSG.LargeExtraspecial.AS35U
end
