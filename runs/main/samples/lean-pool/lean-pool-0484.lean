@[expose] public section

open EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction

theorem aut_bound_on_comp (K : Set ℍ) (hk2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ+ → ℝ,
      Summable u ∧
        ∀ (n : ℕ+) (s : K),
        ‖(derivWithin (fun z : ℂ =>
        iteratedDerivWithin k (fun z : ℂ => (z - (n : ℂ))⁻¹ + (z + n)⁻¹) {z : ℂ | 0 < z.im} z)
        {z : ℂ | 0 < z.im} s)‖ ≤
            u n := by
  by_cases h1 : Set.Nonempty K
  · have H := UpperHalfPlane.subset_verticalStrip_of_isCompact hk2
    obtain ⟨A, B, hB, hAB⟩ := H
    let zAB : ℍ := ⟨⟨A, B⟩, by simp [hB]⟩
    refine ⟨fun a : ℕ+ => 2 * ‖((k + 1)! / r (zAB) ^ (k + 2)) * ((a : ℝ) ^ ((k : ℤ) +2))⁻¹‖,
      ?_, ?_⟩
    conv =>
      enter [1]
      ext a
      rw [norm_mul]
      rw [← mul_assoc]
    · apply Summable.mul_left
      simp only [norm_inv, norm_zpow, RCLike.norm_natCast]
      have : Summable fun (i : ℕ) ↦ ((i : ℝ) ^ ((k : ℤ) + 2))⁻¹ := by
        have := (Real.summable_nat_rpow_inv (p := k + 2)).mpr (by linarith)
        apply this.congr
        intro n
        norm_cast
      apply this.subtype
    intro n s
    rw [← iteratedDerivWithin_succ]
    have HT := iter_div_aut_add n (k + 1) s.1.2
    simp only [Int.cast_natCast, one_div, Pi.add_apply] at HT
    rw [HT]
    apply le_trans (norm_add_le _ _)
    simp_rw [mul_assoc]
    rw [two_mul]
    apply add_le_add
    · simpa using sub_bound s.1 A B hB (hAB s.2) k n
    · simpa using add_bound s.1 A B hB (hAB s.2) k n
  refine ⟨fun _ => 0, summable_zero, ?_⟩
  intro n
  rw [not_nonempty_iff_eq_empty] at h1
  simp_all

end
