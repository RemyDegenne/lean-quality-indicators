namespace P2MW.S_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact

attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open MeasureTheory Set NumberField NumberField.InfinitePlace IsDedekindDomain

open NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicLevel

open AutomorphicForm

open scoped SchwartzMap Classical

noncomputable section

namespace R4PoissonTail

section Assembly

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

local notation "F∞" => InfiniteAdeleRing F

local notation "E∞" => mixedEmbedding.mixedSpace F

local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F

local notation "μ𝔸" => NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F

local notation "GL𝔸" => GL (Fin 2) (AdeleRing (𝓞 F) F)

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem main (φ : GL𝔸 → ℂ) (hφ : IsFactorizableTestFn F φ)
    (Q : Set (GL𝔸 × GL𝔸)) (hQ : IsCompact Q) (N : ℕ) :
    ∃ C : ℝ, ∀ p ∈ Q, ∀ (a : 𝔸ˣ) (t : ℝ), 1 ≤ t → (a : 𝔸).2 = 1 →
      (∀ w : InfinitePlace F, ‖(a : 𝔸).1 w‖ = t) → ∀ e : 𝔸,
        ‖(∑' β : F, φ (p.1 * unipotentGL2 ((ι β + e) * ↑a⁻¹) * p.2)) -
            ((μ𝔸 (adelicBox F)).toReal : ℂ)⁻¹ *
              ∫ u, φ (p.1 * unipotentGL2 ((u + e) * ↑a⁻¹) * p.2) ∂μ𝔸‖
          ≤ C * t⁻¹ ^ N := by
  classical
  obtain ⟨ψ, hψ, hψa⟩ := exists_isGlobalAddChar_std F
  have hψu : ∀ x : 𝔸, ‖ψ x‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ
  obtain ⟨s, hs, hdec⟩ := sliceDecayOn F hφ hψ hψa hQ
  obtain ⟨M, C, hC0, hLS⟩ := NumberField.InfinitePlace.exists_sum_prod_inv_one_add_mul_pow_le F hs (N + 1)
  obtain ⟨B, hB⟩ := hdec M
  set B₀ : ℝ := max B 0 with hB₀def
  have hB₀ : 0 ≤ B₀ := le_max_right _ _
  have hBB₀ : B ≤ B₀ := le_max_left _ _
  set m₀ : ℝ := ‖((((μ𝔸) (adelicBox F)).toReal : ℂ))⁻¹‖ with hm₀def
  refine ⟨m₀ * (B₀ * C), fun p hp a t ht haf haa e => ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  have hnpos : 0 < Module.finrank ℚ F := Module.finrank_pos

  set g : 𝔸 → ℂ := fun v => φ (p.1 * unipotentGL2 v * p.2) with hgdef
  set Ψ : 𝔸 → ℂ := fun v => g (((a⁻¹ : 𝔸ˣ) : 𝔸) * v + ((a⁻¹ : 𝔸ˣ) : 𝔸) * e) with hΨdef
  have hΨ_apply : ∀ v : 𝔸, φ (p.1 * unipotentGL2 ((v + e) * ↑a⁻¹) * p.2) = Ψ v := by
    intro v
    simp only [hΨdef, hgdef]
    rw [show (v + e) * ((a⁻¹ : 𝔸ˣ) : 𝔸) = ((a⁻¹ : 𝔸ˣ) : 𝔸) * v + ((a⁻¹ : 𝔸ˣ) : 𝔸) * e by ring]

  have hΨslice : Ψ = fun v => φ ((p.1 * diagFst a⁻¹)
      * unipotentGL2 v * (diagFst a * unipotentGL2 (((a⁻¹ : 𝔸ˣ) : 𝔸) * e) * p.2)) := by
    funext v
    simp only [hΨdef, hgdef]
    rw [unipotentGL2_add, mul_comm (((a⁻¹ : 𝔸ˣ) : 𝔸)) v, unipotentGL2_mul_eq_conj]
    simp only [mul_assoc]
  have hΨSB : Ψ ∈ schwartzBruhat F := by
    rw [hΨslice]
    exact mem_schwartzBruhat_of_mem_pureTensorSet
      (AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet F hφ _ _)
  have hgSB : g ∈ schwartzBruhat F :=
    mem_schwartzBruhat_of_mem_pureTensorSet
      (AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet F hφ _ _)

  have hP := tsum_eq_inv_measure_mul_tsum_fourierIntegral F μ𝔸 hψ hΨSB
  have hint : Integrable Ψ μ𝔸 := integrable_of_mem_schwartzBruhat F μ𝔸 hΨSB
  have hzero : fourierIntegral ψ μ𝔸 Ψ 0 = ∫ u, Ψ u ∂μ𝔸 := fourierIntegral_zero_right F ψ μ𝔸 Ψ
  have hLHS : (∑' β : F, φ (p.1 * unipotentGL2 ((ι β + e) * ↑a⁻¹) * p.2)) -
        ((μ𝔸 (adelicBox F)).toReal : ℂ)⁻¹ * ∫ u, φ (p.1 * unipotentGL2 ((u + e) * ↑a⁻¹) * p.2) ∂μ𝔸
      = ((μ𝔸 (adelicBox F)).toReal : ℂ)⁻¹ *
          (∑' β : F, fourierIntegral ψ μ𝔸 Ψ (ι β) - fourierIntegral ψ μ𝔸 Ψ 0) := by
    simp_rw [hΨ_apply]
    rw [hP, hzero, mul_sub]
  rw [hLHS]

  have htn : ∏ v : InfinitePlace F, t ^ v.mult = t ^ Module.finrank ℚ F := by
    rw [Finset.prod_pow_eq_pow_sum, NumberField.InfinitePlace.sum_mult_eq]
  have hδ : ((distribHaarChar 𝔸 a⁻¹ : ℝ))⁻¹ = t ^ Module.finrank ℚ F := by
    rw [map_inv, NNReal.coe_inv, inv_inv,
      NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F a haf, ← htn]
    exact Finset.prod_congr rfl fun v _ => by rw [haa v]

  have hG3 : ∀ η : 𝔸, ‖fourierIntegral ψ μ𝔸 Ψ η‖
      = t ^ Module.finrank ℚ F * ‖fourierIntegral ψ μ𝔸 g ((a : 𝔸) * η)‖ := by
    intro η
    have h := norm_fourierIntegral_affine F ψ hψu g a⁻¹ (((a⁻¹ : 𝔸ˣ) : 𝔸) * e) η
    rw [inv_inv] at h
    rw [show Ψ = fun v => g (((a⁻¹ : 𝔸ˣ) : 𝔸) * v + ((a⁻¹ : 𝔸ˣ) : 𝔸) * e) from rfl, h, hδ]

  have hSB : fourierIntegral ψ μ𝔸 Ψ ∈ schwartzBruhat F := fourierIntegral_mem_schwartzBruhat F μ𝔸 hψ hΨSB
  have hsumm : Summable fun ξ : F => fourierIntegral ψ μ𝔸 Ψ (ι ξ) := by
    simpa only [zero_add] using summable_translate_of_mem_schwartzBruhat F hSB 0
  have hsplit := hsumm.tsum_eq_add_tsum_ite 0
  rw [map_zero] at hsplit
  rw [hsplit, add_sub_cancel_left]

  set H : ℝ := t ^ Module.finrank ℚ F with hHdef
  have hH1 : 1 ≤ H := one_le_pow₀ ht
  have hH0 : 0 < H := one_pos.trans_le hH1
  set nrm : F → ℝ := fun ζ => ‖fourierIntegral ψ μ𝔸 g ((a : 𝔸) * ι ζ)‖ with hnrmdef
  set b : F → ℝ := fun ξ => if ξ = 0 then 0 else H * nrm ξ with hbdef
  have hb0 : 0 ≤ b := fun ξ => by
    simp only [hbdef, Pi.zero_apply]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg hH0.le (norm_nonneg _)
  have hpt : ∀ ξ : F, ‖(if ξ = 0 then 0 else fourierIntegral ψ μ𝔸 Ψ (ι ξ))‖ ≤ b ξ := by
    intro ξ
    by_cases hξ : ξ = 0
    · simp [hbdef, hξ]
    · rw [if_neg hξ, hG3]
      simp [hbdef, hnrmdef, hξ, hHdef]
  have hpartial : ∀ u : Finset F, ∑ ξ ∈ u, b ξ ≤ B₀ * C * H⁻¹ ^ N := by
    intro u
    have h1 : ∑ ξ ∈ u, b ξ = H * ∑ ζ ∈ u.filter (· ≠ 0), nrm ζ := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      by_cases hξ : ξ = 0 <;> simp [hbdef, hξ]
    set v : Finset F := u.filter (· ≠ 0) with hvdef
    have hv0 : ∀ ζ ∈ v, ζ ≠ 0 := fun ζ hζ => (Finset.mem_filter.1 hζ).2
    set good : F → Prop := fun ζ => ∃ a' : 𝓞 F, (a' : F) = (s : F) * ζ with hgooddef
    have h2 : ∑ ζ ∈ v, nrm ζ = ∑ ζ ∈ v.filter good, nrm ζ := by
      refine (Finset.sum_filter_of_ne fun ζ hζ hne => ?_).symm
      have hne' : fourierIntegral ψ μ𝔸 g ((a : 𝔸) * ι ζ) ≠ 0 := by
        intro h0; apply hne; simp [hnrmdef, h0]
      exact (hB p hp a t ht haf haa ζ).2 hne'
    have h3 : ∑ ζ ∈ v.filter good, nrm ζ
        ≤ B₀ * ∑ ζ ∈ v.filter good, ∏ w' : InfinitePlace F, ((1 + t * w' ζ) ^ M)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ζ hζ => ?_
      refine ((hB p hp a t ht haf haa ζ).1).trans ?_
      exact mul_le_mul_of_nonneg_right hBB₀ (Finset.prod_nonneg fun w' _ => by positivity)
    have h4 : ∑ ζ ∈ v.filter good, ∏ w' : InfinitePlace F, ((1 + t * w' ζ) ^ M)⁻¹
        ≤ C * ((H) ^ (N + 1))⁻¹ := by
      set yv : InfinitePlace F → ℝ := fun _ => t with hydef
      have hy : ∀ w', yv w' = t := fun _ => rfl
      have hyprod : ∏ w', yv w' ^ w'.mult = H := by rw [hHdef]; exact htn
      have h := hLS yv (fun _ => ht0) (by rw [hyprod]; exact hH1) (v.filter good)
        (fun ζ hζ => ⟨hv0 ζ (Finset.mem_filter.1 hζ).1, (Finset.mem_filter.1 hζ).2⟩)
      rw [hyprod] at h
      simp only [hy] at h
      exact h
    have hkey : H * ((H) ^ (N + 1))⁻¹ = H⁻¹ ^ N := by
      rw [inv_pow, pow_succ, mul_inv, mul_comm ((H ^ N)⁻¹), ← mul_assoc, mul_inv_cancel₀ hH0.ne', one_mul]
    calc ∑ ξ ∈ u, b ξ = H * ∑ ζ ∈ v, nrm ζ := h1
      _ ≤ H * (B₀ * (C * ((H) ^ (N + 1))⁻¹)) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 hB₀)) hH0.le
      _ = B₀ * C * H⁻¹ ^ N := by rw [← hkey]; ring
  have hbsum : Summable b := summable_of_sum_le hb0 hpartial
  have htail : ‖∑' ξ : F, (if ξ = 0 then 0 else fourierIntegral ψ μ𝔸 Ψ (ι ξ))‖ ≤ B₀ * C * H⁻¹ ^ N :=
    (tsum_of_norm_bounded hbsum.hasSum hpt).trans (Real.tsum_le_of_sum_le hb0 hpartial)

  have hHt : H⁻¹ ^ N ≤ t⁻¹ ^ N := by
    refine pow_le_pow_left₀ (inv_nonneg.mpr hH0.le) ?_ N
    rw [hHdef]
    exact inv_anti₀ ht0 (le_self_pow₀ ht hnpos.ne')
  calc ‖((((μ𝔸) (adelicBox F)).toReal : ℂ))⁻¹ *
          ∑' ξ : F, (if ξ = 0 then 0 else fourierIntegral ψ μ𝔸 Ψ (ι ξ))‖
      ≤ m₀ * (B₀ * C * H⁻¹ ^ N) := by
        rw [norm_mul, hm₀def]
        exact mul_le_mul_of_nonneg_left htail (norm_nonneg _)
    _ ≤ m₀ * (B₀ * C * t⁻¹ ^ N) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHt (mul_nonneg hB₀ hC0)) (norm_nonneg _)
    _ = m₀ * (B₀ * C) * t⁻¹ ^ N := by ring

end Assembly
end R4PoissonTail
end
end P2MW.S_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact
