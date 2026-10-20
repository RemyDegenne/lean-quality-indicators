@[expose] public section

noncomputable section

open MeasureTheory

open Homogenization

namespace AVenhance.Infra.Section3

open AVenhance

theorem LMN_zero_unit_average_bounds {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) :
    let T := tauPP β I.Λ m
    let P := tauP β I.Λ m
    let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
    0 ≤ (∫ t in (0 : ℝ)..1, I.LMN κ m 0 t) ∧
      (∫ t in (0 : ℝ)..1, I.LMN κ m 0 t) ≤ ρ⁻¹ ∧
      (((1 / T) * (T - 5 * P)) * ((1 - Real.exp (-ρ * P)) / ρ) ≤
        ∫ t in (0 : ℝ)..1, I.LMN κ m 0 t) := by
  classical
  dsimp only
  let T := tauPP β I.Λ m
  let P := tauP β I.Λ m
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let f : ℝ → ℝ := I.LMN κ m 0
  have hT : 0 < T := by dsimp [T]; exact I.tauPP_pos' m
  have hP : 0 < P := by
    dsimp [P]
    exact Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m)
    positivity
  have hfactor : 5 ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
    unfold Infra.Ingredients.tauCellFactor
    have heps := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m - 1)
    have hpow : 0 < epsilon β I.Λ (m - 1) ^ (-delta β) :=
      Real.rpow_pos_of_pos heps _
    have hceil : 1 ≤ ⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ :=
      Nat.ceil_pos.mpr hpow
    exact_mod_cast (show 5 ≤ 4 * ⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ + 1 by omega)
  have hTP : 5 * P ≤ T := by
    have hscale := Infra.Ingredients.tauPP_eq_cellFactor_mul_tauP
      (β := β) (Λ := I.Λ) hm
    have hfactorReal : (5 : ℝ) ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
      exact_mod_cast hfactor
    dsimp [T, P]
    rw [hscale]
    nlinarith [hP.le]
  have hcont : Continuous f := by
    dsimp [f]
    exact (LMN_contDiff I hm hκ 0).continuous
  have hnonneg (t : ℝ) : 0 ≤ f t := by
    dsimp [f]
    exact OneStepAveraging.LMN_zero_nonneg I hm κ hκ t
  have hup (t : ℝ) : f t ≤ ρ⁻¹ := by
    dsimp [f, ρ]
    exact OneStepAveraging.LMN_zero_le_inv I hm κ hκ t
  have hperiod : Function.Periodic f T := by
    intro t
    dsimp [f, T]
    exact LMN_periodic I κ m 0 t
  obtain ⟨n, hrecipN⟩ := Infra.Ingredients.tauPP_reciprocal_multiple_four
    I.one_lt_beta I.beta_lt I.two_pow_seven_le hm
  let N : ℕ := 4 * n
  have hNperiod : (N : ℝ) * T = 1 := by
    have hrecip : 1 / T = (N : ℝ) := by
      dsimp [T, N]
      exact_mod_cast hrecipN
    have hone : 1 = (N : ℝ) * T := (div_eq_iff hT.ne').mp hrecip
    linarith
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hunit := intervalIntegral_unit_eq_period_mul hperiod hcont hNperiod
  have hcenter : (∫ t in (-(T / 2))..(T / 2), f t) =
      ∫ t in (0 : ℝ)..T, f t := by
    have h := hperiod.intervalIntegral_add_eq (-(T / 2)) 0
    have hend : -(T / 2) + T = T / 2 := by ring
    rw [hend] at h
    simpa only [zero_add] using h
  let lo := -(T / 2) + 3 * P
  let hi := T / 2 - 2 * P
  have hlo : -(T / 2) ≤ lo := by dsimp [lo]; linarith
  have hhi : hi ≤ T / 2 := by dsimp [hi]; linarith
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hwholeInt : IntervalIntegrable f volume (-(T / 2)) (T / 2) :=
    hcont.intervalIntegrable _ _
  have hleftInt : IntervalIntegrable f volume (-(T / 2)) lo :=
    hcont.intervalIntegrable _ _
  have hcoreInt : IntervalIntegrable f volume lo hi := hcont.intervalIntegrable _ _
  have hrightInt : IntervalIntegrable f volume hi (T / 2) := hcont.intervalIntegrable _ _
  have hsplitLeft := intervalIntegral.integral_add_adjacent_intervals hleftInt hcoreInt
  have hsplitRight := intervalIntegral.integral_add_adjacent_intervals
    (hleftInt.trans hcoreInt) hrightInt
  have hleftNonneg : 0 ≤ (∫ t in (-(T / 2))..lo, f t) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t _
    exact hnonneg t
  have hrightNonneg : 0 ≤ (∫ t in hi..(T / 2), f t) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t _
    exact hnonneg t
  have hcorePoint (t : ℝ) (ht : t ∈ Set.uIcc lo hi) :
      (1 - Real.exp (-ρ * P)) / ρ ≤ f t := by
    have ht' : t ∈ Set.Icc lo hi := by
      simpa [Set.uIcc_of_le hlohi] using ht
    dsimp [f, lo, hi]
    exact OneStepAveraging.LMN_zero_ge_core I hm κ hκ T P t rfl rfl ht'
  have hcoreLower : (hi - lo) * ((1 - Real.exp (-ρ * P)) / ρ) ≤
      (∫ t in lo..hi, f t) := by
    have hmono := intervalIntegral.integral_mono_on hlohi intervalIntegrable_const hcoreInt
      (fun t ht => hcorePoint t (by
        simpa [Set.uIcc_of_le hlohi] using ht))
    calc
      (hi - lo) * ((1 - Real.exp (-ρ * P)) / ρ) =
          ∫ t in lo..hi, ((1 - Real.exp (-ρ * P)) / ρ) := by
            rw [intervalIntegral.integral_const]
            simp only [smul_eq_mul]
      _ ≤ _ := hmono
  have hcenterLower :
      (T - 5 * P) * ((1 - Real.exp (-ρ * P)) / ρ) ≤
        (∫ t in (-(T / 2))..(T / 2), f t) := by
    have hlength : hi - lo = T - 5 * P := by dsimp [hi, lo]; ring
    calc
      (T - 5 * P) * ((1 - Real.exp (-ρ * P)) / ρ) ≤
          ∫ t in lo..hi, f t := by rw [← hlength]; exact hcoreLower
      _ ≤ (∫ t in (-(T / 2))..lo, f t) +
            (∫ t in lo..hi, f t) + (∫ t in hi..(T / 2), f t) := by
          have hr : (∫ t in lo..hi, f t) ≤
              (∫ t in lo..hi, f t) + (∫ t in hi..(T / 2), f t) :=
            le_add_of_nonneg_right hrightNonneg
          have hl : (∫ t in lo..hi, f t) + (∫ t in hi..(T / 2), f t) ≤
              (∫ t in (-(T / 2))..lo, f t) +
                ((∫ t in lo..hi, f t) + (∫ t in hi..(T / 2), f t)) :=
            le_add_of_nonneg_left hleftNonneg
          linarith
      _ = ∫ t in (-(T / 2))..(T / 2), f t := by
          rw [← hsplitRight, ← hsplitLeft]
  have hcenterUpper :
      (∫ t in (-(T / 2))..(T / 2), f t) ≤ T * ρ⁻¹ := by
    have hmono := intervalIntegral.integral_mono_on (by linarith [hT]) hwholeInt
      intervalIntegrable_const (fun t _ => hup t)
    calc
      (∫ t in (-(T / 2))..(T / 2), f t) ≤
          ∫ t in (-(T / 2))..(T / 2), ρ⁻¹ := hmono
      _ = T * ρ⁻¹ := by simp [intervalIntegral.integral_const, smul_eq_mul]
  have hperiodUpper : (∫ t in (0 : ℝ)..T, f t) ≤ T * ρ⁻¹ := by
    rw [← hcenter]
    exact hcenterUpper
  have hunitUpper : (∫ t in (0 : ℝ)..1, f t) ≤ ρ⁻¹ := by
    rw [hunit]
    calc
      (N : ℝ) * (∫ t in (0 : ℝ)..T, f t) ≤ (N : ℝ) * (T * ρ⁻¹) :=
        mul_le_mul_of_nonneg_left hperiodUpper hNnonneg
      _ = ρ⁻¹ := by rw [← mul_assoc, hNperiod]; ring
  have hN_eq : (N : ℝ) = 1 / T :=
    (eq_div_iff hT.ne').2 hNperiod
  have hunitLower :
      ((1 / T) * (T - 5 * P)) * ((1 - Real.exp (-ρ * P)) / ρ) ≤
        (∫ t in (0 : ℝ)..1, f t) := by
    calc
      ((1 / T) * (T - 5 * P)) * ((1 - Real.exp (-ρ * P)) / ρ) =
          (N : ℝ) * ((T - 5 * P) * ((1 - Real.exp (-ρ * P)) / ρ)) := by
            rw [hN_eq]
            ring
      _ ≤ (N : ℝ) * (∫ t in (-(T / 2))..(T / 2), f t) :=
        mul_le_mul_of_nonneg_left hcenterLower hNnonneg
      _ = ∫ t in (0 : ℝ)..1, f t := by rw [hunit, hcenter]
  have hunitNonneg : 0 ≤ (∫ t in (0 : ℝ)..1, f t) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t _
    exact hnonneg t
  exact ⟨hunitNonneg, hunitUpper, hunitLower⟩

end AVenhance.Infra.Section3
end
end
