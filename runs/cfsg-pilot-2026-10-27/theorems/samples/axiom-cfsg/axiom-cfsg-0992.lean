public section

namespace CFSG.RankThree.PartOne.K159

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Centralizer

variable {K : Type} [Field K] {m : ℕ}

theorem transvSL_mem_unitriangular {i j : Fin m} (hij : i < j) (c : K) :
    transvSL hij c ∈ unitriangular m K := by
  rw [mem_unitriangular]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [transvSL_coe]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : a ≠ b := hab.ne'
    have h2 : ¬ (i = a ∧ j = b) := fun h => by
      obtain ⟨rfl, rfl⟩ := h
      exact absurd hij (not_lt.2 hab.le)
    simp [h1, h2]
  · rw [transvSL_coe]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h2 : ¬ (i = a ∧ j = a) := fun h => hij.ne (h.1.trans h.2.symm)
    simp [h2]

end Centralizer
end CFSG.RankThree.PartOne.K159
end
