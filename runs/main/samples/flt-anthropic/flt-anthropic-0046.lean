namespace P2MW.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq

attribute [-instance] instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete

set_option autoImplicit false

open ExtCitation

namespace P2mS17LB

variable (q : Nat.Primes)

theorem main (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hqn : ¬ (q : ℕ) ∣ n)
    {ζ α : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ n) (hα : α ^ n = ((q : ℕ) : AlgebraicClosure ℚ)) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F₀ ≤ F ∧ FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧ ζ ∈ F ∧ α ∈ F ∧
      ∀ m : ℕ, φ ^ m ∈ H q F → n * d ∣ m ∧ primeLocalToGlobal q (φ ^ m) α = α := by
  classical
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
    rfl
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.2.ne_zero
  have hα0 : α ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hα; exact hq0 hα.symm

  let Fz : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ ({ζ, α} : Set (AlgebraicClosure ℚ))
  haveI : FiniteDimensional ℚ Fz :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hζFz : ζ ∈ Fz := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert ζ {α})
  have hαFz : α ∈ Fz := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem ζ rfl)
  let F₀' : IntermediateField ℚ (AlgebraicClosure ℚ) := F₀ ⊔ Fz
  haveI : FiniteDimensional ℚ F₀' := IntermediateField.finiteDimensional_sup F₀ Fz

  obtain ⟨F₁, h01, hF₁fd, hK1⟩ :=
    exists_level_dvd_of_frobenius_pow_mem_inertia_sup q φ hφ F₀' (n * d) (Nat.mul_pos hn hd)
  haveI := hF₁fd

  obtain ⟨k, hk⟩ := exists_frobenius_pow_inv_mul_mem_inertia_sup_level q φ hφ F₁ φ⁻¹
  set f₁ : ℕ := k + 1 with hf₁def
  have hψ : φ ^ f₁ ∈ H q F₁ := by
    have : (φ ^ k)⁻¹ * φ⁻¹ = (φ ^ f₁)⁻¹ := by rw [hf₁def, pow_succ', mul_inv_rev]
    rw [this] at hk
    exact (Subgroup.inv_mem_iff _).mp hk
  have hf₁ : 0 < f₁ := Nat.succ_pos k

  obtain ⟨F₂, h12, hF₂fd, hK2⟩ :=
    exists_level_dvd_of_frobenius_pow_mem_inertia_sup q φ hφ F₁ (n * f₁) (Nat.mul_pos hn hf₁)
  haveI := hF₂fd
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F₂ (AlgebraicClosure ℚ)
  have h2F : F₂ ≤ F := IntermediateField.le_normalClosure F₂
  haveI : FiniteDimensional ℚ F := normalClosure.is_finiteDimensional ℚ F₂ (AlgebraicClosure ℚ)
  haveI : Normal ℚ F := normalClosure.normal ℚ F₂ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ F := IsGalois.mk
  have h0F : F₀' ≤ F := h01.trans (h12.trans h2F)
  refine ⟨F, le_sup_left.trans h0F, inferInstance, inferInstance, h0F (le_sup_right (b := Fz) hζFz),
    h0F (le_sup_right (b := Fz) hαFz), fun m hm => ?_⟩
  have hm2 : φ ^ m ∈ H q F₂ := H_anti q h2F hm
  have hm1 : φ ^ m ∈ H q F₁ := H_anti q h12 hm2
  have hm0 : φ ^ m ∈ H q F₀' := H_anti q h01 hm1
  refine ⟨hK1 m hm1, ?_⟩

  obtain ⟨c', hc'⟩ := hK2 m hm2
  set ψ := primeLocalToGlobal q (φ ^ f₁) with hψdef
  have hψζ : ψ ζ = ζ := apply_eq_of_mem_H q hqn hζ.pow_eq_one (h01 (le_sup_right (b := Fz) hζFz)) hψ
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨c, -, hc⟩ : ∃ c : ℕ, c < n ∧ ψ α = ζ ^ c * α := by
    have h1 : (ψ α * α⁻¹) ^ n = 1 := by
      rw [mul_pow, ← map_pow, hα, map_natCast, inv_pow, hα, mul_inv_cancel₀ hq0]
    obtain ⟨c, hc, hζc⟩ := hζ.eq_pow_of_pow_eq_one h1
    exact ⟨c, hc, by rw [hζc, inv_mul_cancel_right₀ hα0]⟩
  have hφm : primeLocalToGlobal q (φ ^ m) = ψ ^ (n * c') := by
    rw [hc', show n * f₁ * c' = f₁ * (n * c') by ring, pow_mul, map_pow]
  rw [hφm, pow_apply_eq hψζ hc (n * c'), show n * c' * c = n * (c' * c) by ring, pow_mul, hζ.pow_eq_one, one_pow,
    one_mul]

end P2mS17LB
end P2MW.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq
