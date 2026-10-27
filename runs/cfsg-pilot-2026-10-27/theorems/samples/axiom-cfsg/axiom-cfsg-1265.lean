public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.OddIso CFSG.RankThree.Classical CFSG.LieType.Chevalley

variable {F n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

section Span

variable {k : Subfield K} [CharP K 2] {A₀ : GL (Fin n) k}

omit h in
theorem fix_le_span_embVec (hodd : Odd p) (hA₀p : linOf A₀ ^ p = 1)
    (hAp : linOf (subfieldGL k n A₀) ^ p = 1) [CharP k 2] :
    LinearMap.ker (linOf (subfieldGL k n A₀) - 1) ≤
      Submodule.span K {x | ∃ w ∈ LinearMap.ker (linOf A₀ - 1), x = embVec k w} := by
  intro v hv
  rw [← range_avg hodd hAp] at hv
  obtain ⟨x, rfl⟩ := hv
  rw [pi_eq_sum_univ x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨avg (linOf A₀) p (Pi.single i 1), ?_, ?_⟩)
  · rw [← range_avg hodd hA₀p]
    exact ⟨_, rfl⟩
  · have := avg_embVec k (A₀ := A₀) p (Pi.single i 1)
    rw [embVec_single] at this
    rw [← this]
    congr 1
    funext j
    simp [Pi.single_apply, eq_comm]

end Span
end CFSG.RankThree.PartOne
end
