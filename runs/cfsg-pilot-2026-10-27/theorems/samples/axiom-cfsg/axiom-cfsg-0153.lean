public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSq

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootSpace CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice

open CFSG.RankThree.E6 (charVal charVal_single charVal_add charVal_neg charVal_smul weylMatrix
  weylMatrix_mulVec eq_of_smul_single_eq)

open scoped Matrix

set_option linter.unusedSectionVars false

section Columns

variable {τ : Tag} {R : Type*} [CommRing R]

theorem exists_eq_add_of_indep {c₀ c₁ : Fin 2 → ZMod 5}
    (h : ∀ a b : ZMod 5, a • c₀ + b • c₁ = 0 → a = 0 ∧ b = 0) (e : Fin 2 → ZMod 5) :
    ∃ a b : ZMod 5, e = a • c₀ + b • c₁ := by
  have hD : c₀ 0 * c₁ 1 - c₀ 1 * c₁ 0 ≠ 0 := by
    intro hD
    have h1 := h (c₁ 1) (-(c₀ 1)) (fin_two_ext
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          linear_combination hD)
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; ring))
    have h2 := h (c₁ 0) (-(c₀ 0)) (fin_two_ext
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; ring)
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          linear_combination (-1 : ZMod 5) * hD))
    have h00 : c₀ 0 = 0 := neg_eq_zero.1 h2.2
    have h01 : c₀ 1 = 0 := neg_eq_zero.1 h1.2
    have h3 := h 1 0 (fin_two_ext
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, h00]; ring)
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, h01]; ring))
    exact absurd h3.1 (by decide)
  obtain ⟨E, hE⟩ : ∃ E : ZMod 5, (c₀ 0 * c₁ 1 - c₀ 1 * c₁ 0) * E = 1 := by
    generalize c₀ 0 * c₁ 1 - c₀ 1 * c₁ 0 = D at hD
    revert D
    decide
  refine ⟨(e 0 * c₁ 1 - e 1 * c₁ 0) * E, (c₀ 0 * e 1 - c₀ 1 * e 0) * E, fin_two_ext ?_ ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-e 0) * hE
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-e 1) * hE

end Columns
end CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSq
end
