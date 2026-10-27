public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint

open CFSG.ABGLocalTools (IsSylowOf)

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

open scoped MatrixGroups

section S313aGeneric

open scoped Matrix

theorem s313a_sq_eq_one_of_fixed {k : Type*} [Field k] (h2 : (2 : k) = 0)
    (M : SL(2, k)) {v : Fin 2 → k} (hv : v ≠ 0)
    (hM : (M : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v) :
    M * M = 1 := by
  have hdet : (M : Matrix (Fin 2) (Fin 2) k).det = 1 := M.2
  have hker : ((M : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hM, Matrix.one_mulVec, sub_self]
  have hd0 : ((M : Matrix (Fin 2) (Fin 2) k) - 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, hker⟩
  rw [Matrix.det_fin_two] at hd0 hdet
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq,
    Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true, sub_zero,
    zero_sub] at hd0
  set a := (M : Matrix (Fin 2) (Fin 2) k) 0 0 with ha
  set b := (M : Matrix (Fin 2) (Fin 2) k) 0 1 with hb
  set c := (M : Matrix (Fin 2) (Fin 2) k) 1 0 with hc
  set d := (M : Matrix (Fin 2) (Fin 2) k) 1 1 with hd
  have had : a + d = 0 := by linear_combination (hdet - hd0) + h2
  have hda : d = a := by linear_combination had - a * h2
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · linear_combination hdet - a * hda + (b * c) * h2
  · linear_combination b * had
  · linear_combination c * had
  · linear_combination hdet + d * hda + (b * c) * h2

end S313aGeneric
end CFSG.LocalAnalysis.EvenBN.U5
end
