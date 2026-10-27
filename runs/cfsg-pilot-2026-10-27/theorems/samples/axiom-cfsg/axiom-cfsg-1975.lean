public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

open scoped Pointwise

section Mats

variable {K : Type} [Field K]

theorem f4B2_Mat_mem_Sp {g : ModGL Tag.F4 K} (hg : g ∈ subsystemGroup Tag.F4 K f4B2Support) :
    (f4B2_data.Mat g)ᵀ * f4B2J0 K * f4B2_data.Mat g = f4B2J0 K := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_f4B2Support i).1 hi with rfl | rfl
      · rw [f4B2_Mat_x2]; exact sp_x2 c
      · rw [f4B2_Mat_x3]; exact sp_x3 c
    · rcases (mem_f4B2Support i).1 hi with rfl | rfl
      · rw [f4B2_Mat_y2]; exact sp_y2 c
      · rw [f4B2_Mat_y3]; exact sp_y3 c
  | one =>
    rw [f4B2_data.Mat_one, transpose_one, Matrix.one_mul, Matrix.mul_one]
  | mul x y hx hy ihx ihy =>
    rw [f4B2_data.Mat_mul hx hy, transpose_mul]
    calc (f4B2_data.Mat y)ᵀ * (f4B2_data.Mat x)ᵀ * f4B2J0 K * (f4B2_data.Mat x * f4B2_data.Mat y)
        = (f4B2_data.Mat y)ᵀ * ((f4B2_data.Mat x)ᵀ * f4B2J0 K * f4B2_data.Mat x) *
            f4B2_data.Mat y := by simp only [Matrix.mul_assoc]
      _ = f4B2J0 K := by rw [ihx, ihy]
  | inv x hx ih =>
    have h := f4B2_data.Mat_mul (inv_mem hx) hx
    rw [inv_mul_cancel, f4B2_data.Mat_one] at h
    calc (f4B2_data.Mat x⁻¹)ᵀ * f4B2J0 K * f4B2_data.Mat x⁻¹
        = (f4B2_data.Mat x⁻¹)ᵀ * ((f4B2_data.Mat x)ᵀ * f4B2J0 K * f4B2_data.Mat x) *
            f4B2_data.Mat x⁻¹ := by rw [ih]
      _ = (f4B2_data.Mat x * f4B2_data.Mat x⁻¹)ᵀ * f4B2J0 K *
            (f4B2_data.Mat x * f4B2_data.Mat x⁻¹) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = f4B2J0 K := by
          have h' : f4B2_data.Mat x * f4B2_data.Mat x⁻¹ = 1 := by
            rw [← f4B2_data.Mat_mul hx (inv_mem hx), mul_inv_cancel, f4B2_data.Mat_one]
          rw [h', transpose_one, Matrix.one_mul, Matrix.mul_one]

end Mats
end CFSG.RankThree.PartOne.KF4
end
