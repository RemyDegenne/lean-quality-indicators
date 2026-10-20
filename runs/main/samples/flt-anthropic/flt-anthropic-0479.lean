namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq

set_option autoImplicit false

set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace E81QM

variable {L : Type*} [Field L] {A : ValuationSubring L}

variable {F : Type*} [Field F] [Algebra L F]

variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

variable (A) in
theorem exists_normalizer {J : Type*} (t : Finset J) (g : J → L) {i₀ : J} (hi₀ : i₀ ∈ t)
    (hg : g i₀ ≠ 0) :
    ∃ i₁ ∈ t, g i₁ ≠ 0 ∧ (∀ i ∈ t, (g i₁)⁻¹ * g i ∈ A) ∧
      (∀ i ∈ t, A.valuation (g i) ≤ A.valuation (g i₁)) := by
  obtain ⟨i₁, hi₁t, hmax⟩ := t.exists_max_image (fun i => A.valuation (g i)) ⟨i₀, hi₀⟩
  have hg₁ : g i₁ ≠ 0 := by
    intro h0; have h := hmax i₀ hi₀
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at h; exact hg h
  have hv₁ : A.valuation (g i₁) ≠ 0 := by rwa [ne_eq, map_eq_zero]
  refine ⟨i₁, hi₁t, hg₁, fun i hi => ?_, hmax⟩
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  calc (A.valuation (g i₁))⁻¹ * A.valuation (g i)
      ≤ (A.valuation (g i₁))⁻¹ * A.valuation (g i₁) := by gcongr; exact hmax i hi
    _ = 1 := inv_mul_cancel₀ hv₁

end E81QM
end
end P2MW.S_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
