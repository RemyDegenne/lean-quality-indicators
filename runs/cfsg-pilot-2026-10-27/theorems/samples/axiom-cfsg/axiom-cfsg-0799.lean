public section

namespace CFSG.RankThree.PartOne.SEITZ4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.SubgroupLists
  CFSG.RankThree.PartOne.CTP

variable {r : ℕ} {K : Type} [Field K]

section Char2

variable [CharP K 2]

theorem rat_step {H : Subgroup (StatedSp r K)} {k : Subfield K} (hH : spSub r k ≤ H)
    {x y : Fin r ⊕ Fin r → K} (hx : x ∈ rootSet H) (hxr : IsRat k x) (hyr : IsRat k y)
    (hxy : spForm r K x y ≠ 0) : y ∈ rootSet H := by
  have hc : (spForm r K x y)⁻¹ ∈ k := k.inv_mem (spForm_mem_of_isRat hxr hyr)
  have hg := hH (spTrans_mem_spSub k (isRat_add hxr hyr) hc)
  have h := mulVec_mem_rootSet hx hg
  have e : spMat (⟨spTrans (x + y) (spForm r K x y)⁻¹, spTrans_mem_statedSp _ _⟩ :
      StatedSp r K) *ᵥ x = y := by
    change spTransMat (x + y) (spForm r K x y)⁻¹ *ᵥ x = y
    rw [spTransMat_mulVec, map_add, spForm_self, zero_add, inv_mul_cancel₀ hxy, one_smul,
      ← add_assoc, add_self_vec, zero_add]
  rwa [e] at h

end Char2
end CFSG.RankThree.PartOne.SEITZ4
end
