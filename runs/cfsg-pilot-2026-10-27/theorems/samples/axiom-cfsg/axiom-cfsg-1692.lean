public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem eq_one_of_fixes_N2 {i n : GL (Fin 4) K} (hi : i ∈ miyamotoI2 h)
    (hn : n ∈ miyamotoN2 h) (hfix : ∀ g ∈ miyamotoN2 h, i * n * g * (i * n)⁻¹ = g) :
    n = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨c, hc, rfl⟩ := mem_rootB_of_fixes h hi hn
    fun b hb => hfix _ (miyamotoRootB_le_N2 h ⟨b, hb, rfl⟩)
  set g := miyamotoN2Hom h (upperSL2 (1 : h.fixedField)) with hg
  have hgN : g ∈ miyamotoN2 h := ⟨_, rfl⟩
  have e := hfix g hgN
  have hig : i * g = g * i := miyamotoI2_commute_N2 h hi hgN
  have e2 : miyamotoXGL h 0 c 0 0 * g = g * miyamotoXGL h 0 c 0 0 := by
    calc miyamotoXGL h 0 c 0 0 * g =
        i⁻¹ * (i * miyamotoXGL h 0 c 0 0 * g * (i * miyamotoXGL h 0 c 0 0)⁻¹) *
          (i * miyamotoXGL h 0 c 0 0) := by group
      _ = i⁻¹ * g * (i * miyamotoXGL h 0 c 0 0) := by rw [e]
      _ = i⁻¹ * (g * i) * miyamotoXGL h 0 c 0 0 := by group
      _ = i⁻¹ * (i * g) * miyamotoXGL h 0 c 0 0 := by rw [hig]
      _ = g * miyamotoXGL h 0 c 0 0 := by group
  have e11 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 1 1) e2
  simp only [Units.val_mul, coe_miyamotoXGL, hg, coe_miyamotoN2Hom_upperSL2] at e11
  simp [miyamotoX, Matrix.mul_apply, Fin.sum_univ_four] at e11
  rw [e11, miyamotoXGL_zero]

end CFSG.LocalAnalysis.EvenBN.U4
end
