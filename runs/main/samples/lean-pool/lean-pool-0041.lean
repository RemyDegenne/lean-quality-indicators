@[expose] public section

open scoped InnerProductSpace ENNReal

open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti

namespace BorelCalculus

section Model

theorem inner_mulLp_comp_eq_tsum (D : MultiplicityDatum ℂ) {h : ℂ → ℂ} (hm : Measurable h)
    {C : ℝ} (hC : ∀ z, ‖h z‖ ≤ C) (V W : Lp ℂ 2 D.measure) {vb wb : ℂ × ℕ → ℂ}
    (hvb : (V : ℂ × ℕ → ℂ) =ᵐ[D.measure] vb) (hwb : (W : ℂ × ℕ → ℂ) =ᵐ[D.measure] wb) :
    ⟪mulLp D.measure (hm.comp (measurable_datumSymbol D))
        (fun p => hC (datumSymbol D p)) V, W⟫_ℂ
      = ∑' n, ∫ z, (starRingEnd ℂ) (h z * vb (z, n)) * wb (z, n)
          ∂(D.base.restrict (D.level n)) := by
  have hae : ∀ᵐ p ∂D.measure,
      (starRingEnd ℂ) (h (datumSymbol D p) * (V : ℂ × ℕ → ℂ) p) * (W : ℂ × ℕ → ℂ) p
        = (starRingEnd ℂ) (h p.1 * vb p) * wb p := by
    filter_upwards [ae_datumSymbol_eq_fst D, hvb, hwb] with p h1 h2 h3
    rw [h1, h2, h3]
  have hJint : Integrable (fun p => (starRingEnd ℂ) (h p.1 * vb p) * wb p) D.measure := by
    have hI := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      (mulLp D.measure (hm.comp (measurable_datumSymbol D))
        (fun p => hC (datumSymbol D p)) V) W
    refine hI.congr ?_
    filter_upwards [coeFn_mulLp D.measure (hm.comp (measurable_datumSymbol D))
      (fun p => hC (datumSymbol D p)) V, hae] with p h1 h2
    rw [RCLike.inner_apply, h1, ← h2]
    simp only [Function.comp_apply]
    ring
  calc ⟪mulLp D.measure (hm.comp (measurable_datumSymbol D))
        (fun p => hC (datumSymbol D p)) V, W⟫_ℂ
      = ∫ p, (starRingEnd ℂ) (h (datumSymbol D p) * (V : ℂ × ℕ → ℂ) p)
          * (W : ℂ × ℕ → ℂ) p ∂D.measure :=
        inner_mulLp_left D.measure (hm.comp (measurable_datumSymbol D))
          (fun p => hC (datumSymbol D p)) V W
    _ = ∫ p, (starRingEnd ℂ) (h p.1 * vb p) * wb p ∂D.measure := integral_congr_ae hae
    _ = ∑' n, ∫ z, (starRingEnd ℂ) (h z * vb (z, n)) * wb (z, n)
          ∂(D.base.restrict (D.level n)) := by
        rw [MultiplicityDatum.measure_def] at hJint ⊢
        exact integral_sliceSum _ hJint

end Model
end BorelCalculus
end TauCeti
end
