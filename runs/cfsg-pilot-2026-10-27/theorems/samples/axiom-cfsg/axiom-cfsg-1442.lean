public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag

open scoped Matrix

theorem Fsub_le_closure_conj_x₁ :
    Fsub ≤ closure (Set.range conjX₁) := by
  have hmem : ∀ c, conjX₁ c ∈ closure (Set.range conjX₁) := fun c => subset_closure ⟨c, rfl⟩
  have h4 : x₄SU 0 1 zero_one_rel ∈ closure (Set.range conjX₁) := by
    rw [x₄_eq_conjX₁]
    exact mul_mem (mul_mem (mul_mem (hmem _) (hmem _)) (hmem _)) (hmem _)
  rw [← closure_genFSU, closure_le]
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · change x₁SU 0 1 zero_one_rel ∈ _
    rw [x₁_eq_conjX₁]
    exact hmem 0
  · change x₃SU 1 ∈ _
    rw [x₃_eq_conjX₁ 1 one_ne_zero]
    exact mul_mem (mul_mem (hmem _) (hmem _)) h4
  · change x₃SU F4.ω ∈ _
    rw [x₃_eq_conjX₁ F4.ω (by decide)]
    exact mul_mem (mul_mem (hmem _) (hmem _)) h4
  · exact h4

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
end
