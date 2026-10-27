public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary

open CFSG.Assembly.LowTwoRank (StatedSp)

open CFSG.ClassicalInvolution.PhanD4 (exists_normOne_sq_ne_one mem_range_torusTwo_of_commute
  exists_embSUid_torus_of_commute conjDiag_one)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  {C : B2Coord hK F h2} {G : Type} [Group G] (S : PhanFamilyB3 C G)

variable {S}

section Inf

variable (hq : 3 ≤ p ^ f)

include hK hq in
theorem GoodFamily.exists_tor_of_far (hg : GoodFamily S) {A B : Su K p f 2}
    (hT : S.ι 0 A * S.ι 2 B ∈ torusSub S) :
    ∃ y w, S.ι 0 A * S.ι 2 B = tor S 0 y * tor S 2 w := by
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK hq
  have hc := torusSub_comm S (tor_mem_torusSub S 0 x₀) hT
  have hc2 := torusSub_comm S (tor_mem_torusSub S 2 x₀) hT
  have h11 : (![1, 1] : Fin 2 → normOne (unitaryInvolution K p f)) = 1 := by
    ext i
    fin_cases i <;> rfl
  have e1 : tor S 0 x₀ * (S.ι 0 A * S.ι 2 B) * (tor S 0 x₀)⁻¹ =
      S.ι 0 (conjDiag hK ![x₀ * x₀, 1] A) * S.ι 2 B := by
    have h := tor_conj_ι S 0 2 x₀ B
    rw [chi_zero_two] at h
    rw [show tor S 0 x₀ * (S.ι 0 A * S.ι 2 B) * (tor S 0 x₀)⁻¹ =
      (tor S 0 x₀ * S.ι 0 A * (tor S 0 x₀)⁻¹) * (tor S 0 x₀ * S.ι 2 B * (tor S 0 x₀)⁻¹) by group,
      tor_conj_self S 0 x₀ A, h, h11, conjDiag_one hK B]
  have e2 : tor S 2 x₀ * (S.ι 0 A * S.ι 2 B) * (tor S 2 x₀)⁻¹ =
      S.ι 0 A * S.ι 2 (conjDiag hK ![x₀ * x₀, 1] B) := by
    have h := tor_conj_ι S 2 0 x₀ A
    rw [chi_two_zero] at h
    rw [show tor S 2 x₀ * (S.ι 0 A * S.ι 2 B) * (tor S 2 x₀)⁻¹ =
      (tor S 2 x₀ * S.ι 0 A * (tor S 2 x₀)⁻¹) * (tor S 2 x₀ * S.ι 2 B * (tor S 2 x₀)⁻¹) by group,
      tor_conj_self S 2 x₀ B, h, h11, conjDiag_one hK A]
  have f1 : S.ι 0 (conjDiag hK ![x₀ * x₀, 1] A) * S.ι 2 B = S.ι 0 A * S.ι 2 B := by
    rw [← e1]
    exact mul_inv_eq_iff_eq_mul.mpr hc
  have f2 : S.ι 0 A * S.ι 2 (conjDiag hK ![x₀ * x₀, 1] B) = S.ι 0 A * S.ι 2 B := by
    rw [← e2]
    exact mul_inv_eq_iff_eq_mul.mpr hc2
  have g1 : tor S 0 x₀ * S.ι 0 A = S.ι 0 A * tor S 0 x₀ := by
    apply mul_inv_eq_iff_eq_mul.mp
    rw [tor_conj_self S 0 x₀ A]
    exact mul_right_cancel f1
  have g2 : tor S 2 x₀ * S.ι 2 B = S.ι 2 B * tor S 2 x₀ := by
    apply mul_inv_eq_iff_eq_mul.mp
    rw [tor_conj_self S 2 x₀ B]
    exact mul_left_cancel f2
  obtain ⟨y, hy⟩ := hg.exists_tor_of_comm 0 hx₀ g1
  obtain ⟨w, hw⟩ := hg.exists_tor_of_comm 2 hx₀ g2
  exact ⟨y, w, by rw [hy, hw]⟩

end Inf
end CFSG.ClassicalInvolution.PhanB3
end
