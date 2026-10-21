namespace OAI

noncomputable section

namespace StronglyRationalVOA.WeakModule

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : Type v} [AddCommGroup W] [Module ℂ W]
  {A : VertexAlgebra V} (M : WeakModule A W)

theorem translation_covariance (a : V) (k : ℤ) :
    mode M.fields (A.translation a) k = -(k : ℂ) • mode M.fields a (k-1) := by
  ext x
  change mode M.fields (mode A.fields a (-2) A.vacuum) k x = _
  rw [M.mode_iterate]
  have hcoef (j : ℕ) : (-1 : ℂ)^j * Ring.choose (-2 : ℂ) j = (j : ℂ)+1 := by
    rw [show (-2 : ℂ)=-(2 : ℂ) by ring, Ring.choose_neg', Ring.multichoose_two]
    simp only [Units.smul_def, Int.coe_negOnePow_natCast, zsmul_eq_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one]
    calc
      _ = ((-1 : ℂ)*(-1))^j*((j : ℂ)+1) := by rw [mul_pow]; ring
      _ = _ := by norm_num
  have hn : (-1 : ℂ)^(-2 : ℤ)=1 := by norm_num
  simp only [Int.cast_neg, Int.cast_ofNat, hcoef, hn, one_smul]
  by_cases hk : k < 0
  · let j : ℕ := (-k-1).toNat
    have hj : (j : ℤ) = -k-1 := Int.toNat_of_nonneg (by omega)
    rw [finsum_eq_single _ j (by
      intro i hi
      have h1 : k+(i : ℤ) ≠ -1 := by intro he; apply hi; omega
      have h2 : -2+k-(i : ℤ) ≠ -1 := by omega
      rw [M.vacuum_mode, ite_eq_right h1, M.vacuum_mode, ite_eq_right h2]
      simp)]
    rw [M.vacuum_mode, ite_eq_left (by omega), M.vacuum_mode, ite_eq_right (by omega)]
    simp only [Module.End.one_apply, LinearMap.zero_apply, sub_zero,
      LinearMap.smul_apply]
    rw [show -2-(j : ℤ)=k-1 by omega]
    congr 1
    have hjc : (j : ℂ)=-(k : ℂ)-1 := by exact_mod_cast hj
    rw [hjc]; ring
  · by_cases hk0 : k=0
    · subst k
      rw [finsum_eq_zero_of_forall_eq_zero (by
        intro i
        rw [M.vacuum_mode, ite_eq_right (by omega), M.vacuum_mode, ite_eq_right (by omega)]
        simp)]
      simp
    · let j : ℕ := (k-1).toNat
      have hj : (j : ℤ) = k-1 := Int.toNat_of_nonneg (by omega)
      rw [finsum_eq_single _ j (by
        intro i hi
        have h1 : k+(i : ℤ) ≠ -1 := by omega
        have h2 : -2+k-(i : ℤ) ≠ -1 := by intro he; apply hi; omega
        rw [M.vacuum_mode, ite_eq_right h1, M.vacuum_mode, ite_eq_right h2]
        simp)]
      rw [M.vacuum_mode, ite_eq_right (by omega), M.vacuum_mode, ite_eq_left (by omega)]
      simp only [LinearMap.zero_apply, map_zero, Module.End.one_apply, zero_sub,
        smul_neg, LinearMap.smul_apply]
      rw [hj, ← neg_smul]
      congr 1
      have hjc : (j : ℂ)=(k : ℂ)-1 := by exact_mod_cast hj
      rw [hjc]; ring

end StronglyRationalVOA.WeakModule
end
end OAI
