public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.Sec13

open CritProof

open scoped commutatorElement

section GlueA

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {p : ℕ}
  {C : Subgroup (CFSG.pCore p L)}

theorem dPrime_le_dOf (hcrit : Crit135 L p C) {z : G} (hz : z ∈ L) :
    dPrime L p C z ≤ dOf L p C := by
  unfold dPrime
  rw [Subgroup.commutator_le]
  intro d hd k hk
  have hkL : k ∈ L := Subgroup.zpowers_le.mpr hz hk
  have key : ⁅d, k⁆ = d * (k * d⁻¹ * k⁻¹) := by
    rw [commutatorElement_def]
    simp only [mul_assoc]
  rw [key]
  exact mul_mem hd (ga_conj_mem_dOf hcrit hkL (inv_mem hd))

end GlueA
end CFSG.RankThree.PartTwo.Sec13.F135Last
end
