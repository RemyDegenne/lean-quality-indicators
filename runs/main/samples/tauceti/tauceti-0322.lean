public section

open scoped NNReal

namespace TauCeti.WittVector

open _root_.WittVector TauCeti.Huber

variable (p : ℕ) [Fact p.Prime] {O : Type*} [CommRing O] (ϖ : O)

local notation "𝕎" => _root_.WittVector p

section Interval

variable {p ϖ} {K : Type*} [Field K] [Algebra O K] {v : Valuation K ℝ≥0}
  [CharP O p] [PerfectRing O p] {q q' : ℚ≥0}

variable (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ : ℝ≥0}
  (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)

local notation "L" => IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂

theorem isOpen_windowSubring (h₁ : ρ₁ ^ q.num ≤ v (algebraMap O K ϖ) ^ q.den)
    (h₂ : v (algebraMap O K ϖ) ^ q'.den ≤ ρ₂ ^ q'.num) (hq' : q' ≠ 0) :
    IsOpen (windowSubring p ϖ L q q' : Set L) := by
  set N := q.den + q'.den
  set k := N * q'.num
  -- `x = ([ϖ] ^ N x') ([ϖ] ^ -N p ^ k)` with `x' = x / p ^ k`, and `[ϖ] ^ -N p ^ k` is
  -- `(p ^ a' / [ϖ] ^ b') ^ N [ϖ] ^ (N (b' - 1))`
  have hmem : ∀ x : L, ‖x‖ < min ((ρ₁ : ℝ) ^ k) ((ρ₂ : ℝ) ^ k) →
      x ∈ windowSubring p ϖ L q q' := by
    intro x hx
    set x' := x * mono p ϖ L 0 (-k)
    have hxx' : x = x' * algebraMap (𝕎 O) L ((p : 𝕎 O) ^ k) := by
      rw [← mono_natCast_zero_left (ϖ := ϖ), mul_assoc, ← mono_add]
      simp [mono_zero]
    have hlam {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1)
        (hlt : (gaussValuationAway p hv hϖ ρ hρ L x : ℝ) < ρ ^ k) :
        gaussValuationAway p hv hϖ ρ hρ L x' ≤ 1 := by
      have e := congrArg (gaussValuationAway p hv hϖ ρ hρ L) hxx'
      rw [map_mul, gaussValuationAway_algebraMap, map_pow, gaussValuation_p] at e
      rw [e] at hlt
      exact_mod_cast ((mul_lt_iff_lt_one_left (pow_pos (by exact_mod_cast hρ.1) k)).mp
        (by exact_mod_cast hlt)).le
    have hx' : ‖x'‖ ≤ 1 := by
      rw [IntervalLocalization.norm_def] at hx ⊢
      rw [lt_min_iff, max_lt_iff, max_lt_iff] at hx
      exact max_le (by exact_mod_cast hlam hρ₁ hx.1.1) (by exact_mod_cast hlam hρ₂ hx.2.2)
    have hN := algebraMap_teichmuller_pow_mul_mem_windowSubring_of_norm_le_one hv hϖ hϖ' hρ₁ hρ₂
      h₁ h₂ hq' hx'
    have hx_eq : x = algebraMap (𝕎 O) L (teichmuller p ϖ ^ N) * x' *
        (algebraMap (𝕎 O) L 1 * mono p ϖ L (-N) k) := by
      rw [map_one, one_mul, ← mono_natCast_zero_right (p := p), mul_comm _ x', mul_assoc,
        ← mono_add]
      simp [x', mul_assoc, ← mono_add, mono_zero]
    rw [hx_eq]
    refine Subring.mul_mem _ hN (algebraMap_mul_mono_mem_windowSubring 1 0 N (N * (q'.den - 1)) 0
      ?_ ?_)
    · push_cast [Nat.cast_sub q'.den_pos]; ring
    · simp [k]
  refine AddSubgroup.isOpen_of_mem_nhds (windowSubring p ϖ L q q').toAddSubgroup
    (g := 0) (Filter.mem_of_superset (Metric.ball_mem_nhds 0 (lt_min ?_ ?_)) fun x hx ↦
      hmem x (by simpa using hx))
  · exact pow_pos (by exact_mod_cast hρ₁.1) k
  · exact pow_pos (by exact_mod_cast hρ₂.1) k

end Interval
end TauCeti.WittVector
end
