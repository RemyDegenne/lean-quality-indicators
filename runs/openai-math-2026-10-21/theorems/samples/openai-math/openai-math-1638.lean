namespace OAI

section

noncomputable section

namespace SKGap

open Matrix Real Set

open scoped BigOperators SchwartzMap

lemma wordMarkedCost_uniform (B : NNReal) (j R A c : ℝ) (L : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ z∈Icc (0:ℝ) 1,∀ p≤L,∀ q≤L,
      wordMarkedCost B j R A c z p q≤C := by
  let H : ℝ→ℝ := fun z=>∑ p∈Finset.range (L+1),∑ q∈Finset.range (L+1),|wordMarkedCost B j R A c z p q|
  have hH : Continuous H := by
    unfold H
    exact continuous_finsetSum _ (fun p _=>continuous_finsetSum _ (fun q _=>(continuous_wordMarkedCost B j R A c p q).abs))
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hH.continuousOn
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro z hz p hp q hq
  have hb : wordMarkedCost B j R A c z p q≤H z := by
    calc
      _ ≤ |wordMarkedCost B j R A c z p q| := le_abs_self _
      _ ≤ ∑ r∈Finset.range (L+1),|wordMarkedCost B j R A c z p r| :=
        Finset.single_le_sum (f := fun r=>|wordMarkedCost B j R A c z p r|) (fun _ _=>abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
      _ ≤ H z := by
        dsimp only [H]
        exact Finset.single_le_sum (f := fun w=>∑ r∈Finset.range (L+1),|wordMarkedCost B j R A c z w r|) (fun w _=>Finset.sum_nonneg (fun r _=>abs_nonneg (wordMarkedCost B j R A c z w r)))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hp))
  have hbH : |H z|≤C := hC z hz
  exact hb.trans ((le_abs_self _).trans (hbH.trans (le_max_right _ _)))

end SKGap
end
end
end OAI
