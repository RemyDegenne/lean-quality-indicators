@[expose] public section

noncomputable section

open MeasureTheory

theorem eigenvector_constant_sign {Ω : Type*} [MeasureSpace Ω]
    (T : Lp ℝ 2 (volume : Measure (Ω)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Ω)))
    (hT_compact : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T)
    (hT_pi : IsPositivityImproving' T)
    (f : Lp ℝ 2 (volume : Measure (Ω)))
    (hf_ne : f ≠ 0)
    (lam₀ : ℝ) (hlam₀ : 0 < lam₀)
    (hf_eigen : (T : Lp ℝ 2 (volume : Measure (Ω)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Ω))) f = lam₀ • f)
    (hlam₀_top : ∀ (g : Lp ℝ 2 (volume : Measure (Ω))),
      @inner ℝ _ _ g (T g) ≤ lam₀ * ‖g‖ ^ 2) :
    (∀ᵐ x ∂(volume : Measure (Ω)), 0 < (f : (Ω) → ℝ) x) ∨
    (∀ᵐ x ∂(volume : Measure (Ω)), (f : (Ω) → ℝ) x < 0) := by
  set g := |f| - f with g_def
  -- g ≥ 0: |f(x)| ≥ f(x) pointwise
  have hg_nonneg : 0 ≤ g := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [Lp.coeFn_sub (|f| : Lp ℝ 2 _) f, Lp.coeFn_abs f] with x hsub habs
    rw [show (g : (Ω) → ℝ) x = ((|f| - f : Lp ℝ 2 _) : (Ω) → ℝ) x from rfl,
        hsub]
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [habs, sub_nonneg]
    exact le_abs_self _
  -- T|f| = lam₀|f| from Phase 3
  have hf_abs_eigen : (T : _ →ₗ[ℝ] _) |f| = lam₀ • |f| :=
    abs_eigenvector_of_top_eigenvector T hT_compact hT_sa hT_pi.toPreserving
      f hf_ne lam₀ hlam₀ hf_eigen hlam₀_top
  -- Tg = lam₀ g by linearity
  have hg_eigen : (T : _ →ₗ[ℝ] _) g = lam₀ • g := by
    change (T : _ →ₗ[ℝ] _) (|f| - f) = lam₀ • (|f| - f)
    rw [map_sub, hf_abs_eigen, hf_eigen, smul_sub]
  by_cases hg_eq : g = 0
  · -- g = 0, so |f| = f, hence f ≥ 0 and f ≠ 0
    left
    have hf_eq_abs : |f| = f := by rwa [sub_eq_zero] at hg_eq
    have hf_nonneg : 0 ≤ f := by
      rw [← hf_eq_abs, ← Lp.coeFn_nonneg]
      filter_upwards [Lp.coeFn_abs f] with x habs
      rw [habs]; exact abs_nonneg _
    exact ground_state_strictly_positive T hT_pi f hf_ne hf_nonneg lam₀ hlam₀ hf_eigen
  · -- g ≠ 0, so g > 0 a.e. by Phase 4, meaning |f(x)| > f(x), so f(x) < 0
    right
    have hg_pos := ground_state_strictly_positive T hT_pi g hg_eq hg_nonneg lam₀ hlam₀ hg_eigen
    filter_upwards [hg_pos, Lp.coeFn_sub (|f| : Lp ℝ 2 _) f,
        Lp.coeFn_abs f] with x hx hsub habs
    -- 0 < g(x) = |f(x)| - f(x), so f(x) < 0
    rw [show (g : (Ω) → ℝ) x = ((|f| - f : Lp ℝ 2 _) : (Ω) → ℝ) x from rfl,
        hsub] at hx
    simp only [Pi.sub_apply] at hx
    rw [habs] at hx
    -- hx : 0 < |f x| - f x. If f x ≥ 0, then |f x| = f x, contradiction.
    by_contra h_ge; push Not at h_ge
    linarith [abs_of_nonneg h_ge]

end
end
