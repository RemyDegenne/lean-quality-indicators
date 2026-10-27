public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix Module

open Classical in
theorem gram_invertible_dyadic :
    (Matrix.of fun k l => bform (basisB k) (basisB l)) * Matrix.diagonal (fun k => (gramDiag k)⁻¹) = 1 ∧
      (∀ k l, (Matrix.of fun k l => bform (basisB k) (basisB l)) k l ∈ dyadic) ∧
      ∀ k l, Matrix.diagonal (fun k => (gramDiag k)⁻¹) k l ∈ dyadic := by
  have hG : (Matrix.of fun k l => bform (basisB k) (basisB l)) = Matrix.diagonal gramDiag := by
    ext k l
    rw [of_apply, bform_basisB, Matrix.diagonal_apply]
  refine ⟨?_, fun k l => ?_, fun k l => ?_⟩
  · rw [hG, Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one with k
    rcases gramDiag_mem k with h | h <;> rw [h] <;> norm_num
  · rw [hG, Matrix.diagonal_apply]
    split_ifs
    · rcases gramDiag_mem k with h | h <;> rw [h]
      · exact dyadic.one_mem
      · have h2 : (2 : ℚ) = 1 + 1 := by norm_num
        rw [h2]
        exact dyadic.add_mem dyadic.one_mem dyadic.one_mem
    · exact dyadic.zero_mem
  · rw [Matrix.diagonal_apply]
    split_ifs
    · rcases gramDiag_mem k with h | h <;> rw [h]
      · simpa using dyadic.one_mem
      · exact two_mem_dyadic_inv
    · exact dyadic.zero_mem

end CFSG.Monster.Griess
end
