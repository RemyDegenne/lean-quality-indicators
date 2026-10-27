public section

namespace CFSG.OddStandard.ThmC.T

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

open scoped commutatorElement

theorem closure_gens : Subgroup.closure ({g1, g2, g3, g4} : Set Tc) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  set S := Subgroup.closure ({g1, g2, g3, g4} : Set Tc) with hS
  have h1 : g1 ∈ S := Subgroup.subset_closure (by simp)
  have h2 : g2 ∈ S := Subgroup.subset_closure (by simp)
  have h3 : g3 ∈ S := Subgroup.subset_closure (by simp)
  have h4 : g4 ∈ S := Subgroup.subset_closure (by simp)
  have hA : ∀ a : F4c, (⟨a, 0, 0⟩ : Tc) ∈ S := by
    intro a
    rcases F4c_cases a with rfl | rfl | rfl | rfl
    · exact S.one_mem
    · exact h1
    · exact h2
    · have : (⟨1 + ω, 0, 0⟩ : Tc) = g1 * g2 := by
        refine UT3.ext ?_ ?_ ?_ <;> simp [g1, g2, UT3.mul_def]
      rw [this]; exact S.mul_mem h1 h2
  have hB : ∀ b : F4c, (⟨0, b, 0⟩ : Tc) ∈ S := by
    intro b
    rcases F4c_cases b with rfl | rfl | rfl | rfl
    · exact S.one_mem
    · exact h3
    · exact h4
    · have : (⟨0, 1 + ω, 0⟩ : Tc) = g3 * g4 := by
        refine UT3.ext ?_ ?_ ?_ <;> simp [g3, g4, UT3.mul_def]
      rw [this]; exact S.mul_mem h3 h4
  have hZ : ∀ c : F4c, (⟨0, 0, c⟩ : Tc) ∈ S := by
    have e1 : ⁅g1, g3⁆ = (⟨0, 0, 1⟩ : Tc) := by rw [comm_eq]; ext <;> simp [g1, g3]
    have e2 : ⁅g1, g4⁆ = (⟨0, 0, ω⟩ : Tc) := by rw [comm_eq]; ext <;> simp [g1, g4]
    have m1 : (⟨0, 0, 1⟩ : Tc) ∈ S := by
      rw [← e1, commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem h1 h3) (S.inv_mem h1)) (S.inv_mem h3)
    have m2 : (⟨0, 0, ω⟩ : Tc) ∈ S := by
      rw [← e2, commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem h1 h4) (S.inv_mem h1)) (S.inv_mem h4)
    intro c
    rcases F4c_cases c with rfl | rfl | rfl | rfl
    · exact S.one_mem
    · exact m1
    · exact m2
    · have : (⟨0, 0, 1 + ω⟩ : Tc) = ⟨0, 0, 1⟩ * ⟨0, 0, ω⟩ := by
        refine UT3.ext ?_ ?_ ?_ <;> simp [UT3.mul_def]
      rw [this]; exact S.mul_mem m1 m2
  rw [decomp x]
  exact S.mul_mem (S.mul_mem (hA _) (hB _)) (hZ _)

end CFSG.OddStandard.ThmC.T
end
