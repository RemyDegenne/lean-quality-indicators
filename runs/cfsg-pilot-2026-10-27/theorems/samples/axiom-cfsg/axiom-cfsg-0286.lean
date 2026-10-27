public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv Equiv.Perm

theorem zpowers_allOnes_inf_coreMod_seven :
    Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7 = ⊥ := by
  rw [eq_bot_iff]
  rintro m ⟨hm1, hm2⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm1
  have hm2' : G6.allOnes 7 ^ k ∈ G6.coreMod 7 := hm2
  rw [G6.mem_coreMod] at hm2'
  have hc : ∀ i, Multiplicative.toAdd (G6.allOnes 7 ^ k) i = (k : ZMod 2) := fun i => by
    rw [toAdd_zpow, G6.allOnes, toAdd_ofAdd, Pi.smul_apply, zsmul_eq_mul, mul_one]
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hm2'
  have hk : (k : ZMod 2) = 0 := by
    have h7 : ((7 : ℕ) : ZMod 2) = 1 := by decide
    rwa [h7, one_mul] at hm2'
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  funext i
  rw [hc, hk]
  rfl

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
end
