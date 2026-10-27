public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2119End6Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.RankThreeEven (projSL)

open CFSG.RankThree.Asc83Table (Automizer automizerCongr)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_zpowers_of_commute {e g : G} (h : g * e = e * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
  have hc : ∀ k : ℤ, g * e ^ k * g⁻¹ = e ^ k := fun k => by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h, mul_inv_cancel_right]
  refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, (hc k).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc e ^ k = g⁻¹ * (g * e ^ k * g⁻¹) * g := by group
      _ = g⁻¹ * e ^ k * g := by rw [hc k]
      _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hk]
      _ = y := by group

end CFSG.RankThree.PartTwo.Sec21.Item2119End6Proof
end
