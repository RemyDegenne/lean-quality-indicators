set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {I : Type u} [NonUnitalRing I]

variable {n : Type v} [Fintype n] [DecidableEq n]

theorem isUnit_one_add_unitizationMatrix_iff_isQuasiregular
    (x : Matrix n n I) :
    IsUnit (1 + unitizationMatrix x : Matrix n n (Unitization ℤ I)) ↔
      IsQuasiregular x := by
  rw [isQuasiregular_iff]
  constructor
  · intro hx
    rw [isUnit_iff_exists] at hx
    obtain ⟨z, hxz, hzx⟩ := hx
    have hzfst : matrixFst z = 1 := by
      have h := congrArg matrixFst hxz
      rw [matrixFst_mul, matrixFst_one_add_unitizationMatrix] at h
      simpa [matrixFst] using h
    let y : Matrix n n I := matrixSnd z
    refine ⟨y, ?_, ?_⟩
    · have h := congrArg matrixSnd hxz
      rw [matrixSnd_mul_of_fst_eq_one _ _
        (matrixFst_one_add_unitizationMatrix x) hzfst, matrixSnd_one] at h
      simpa [matrixSnd_one_add_unitizationMatrix, y, add_comm x y] using h
    · have h := congrArg matrixSnd hzx
      rw [matrixSnd_mul_of_fst_eq_one _ _ hzfst
        (matrixFst_one_add_unitizationMatrix x), matrixSnd_one] at h
      simpa [matrixSnd_one_add_unitizationMatrix, y, add_comm x y] using h
  · rintro ⟨y, hyx, hxy⟩
    rw [isUnit_iff_exists]
    refine ⟨1 + unitizationMatrix y, ?_, ?_⟩
    · apply matrix_ext
      · rw [matrixFst_mul, matrixFst_one_add_unitizationMatrix,
          matrixFst_one_add_unitizationMatrix]
        simp [matrixFst]
      · rw [matrixSnd_mul_of_fst_eq_one _ _
          (matrixFst_one_add_unitizationMatrix x)
          (matrixFst_one_add_unitizationMatrix y),
          matrixSnd_one_add_unitizationMatrix,
          matrixSnd_one_add_unitizationMatrix, matrixSnd_one]
        simpa only [add_comm x y] using hyx
    · apply matrix_ext
      · rw [matrixFst_mul, matrixFst_one_add_unitizationMatrix,
          matrixFst_one_add_unitizationMatrix]
        simp [matrixFst]
      · rw [matrixSnd_mul_of_fst_eq_one _ _
          (matrixFst_one_add_unitizationMatrix y)
          (matrixFst_one_add_unitizationMatrix x),
          matrixSnd_one_add_unitizationMatrix,
          matrixSnd_one_add_unitizationMatrix, matrixSnd_one]
        simpa only [add_comm x y] using hxy

end Matrix.GeneralLinearGroup
end
