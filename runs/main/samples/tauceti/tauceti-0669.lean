public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace

open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : C(E, ℝ)} {K : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem W1p.gradient_normalEpigraphExtensionL_ae (hφ : LipschitzWith K φ)
    (u : W1p volume (normalEpigraph φ) p) :
    let Φ := graphFlattening φ φ.continuous
    W1p.gradient (W1p.normalEpigraphExtensionL hφ u) =ᵐ[volume] fun x =>
      if φ x.snd < x.fst then W1p.gradient u x
      else if x.fst < φ x.snd then
        ContinuousLinearMap.adjoint (fderiv ℝ Φ x)
          (normalLinearReflection E
            (ContinuousLinearMap.adjoint (fderiv ℝ Φ.symm (normalReflection E 0 (Φ x)))
              (W1p.gradient u (WithLp.toLp 2 (2 * φ x.snd - x.fst, x.snd)))))
      else 0 := by
  let Φ := graphFlattening φ φ.continuous
  let H := (normalHalfSpace (E := E) 0 : Set (WithLp 2 (ℝ × E)))
  let v := W1p.normalEpigraphEquivL hφ u
  have hflat : H.indicator (W1p.gradient v) =ᵐ[volume]
      H.indicator (fun z => ContinuousLinearMap.adjoint (fderiv ℝ Φ.symm z)
        (W1p.gradient u (Φ.symm z))) :=
    (ae_eq_restrict_iff_indicator_ae_eq (normalHalfSpace (E := E) 0).isOpen.measurableSet).mp
      (W1p.gradient_normalEpigraphEquivL_ae hφ u)
  have horiginal := W1p.gradient_restrictL_ae (le_top : normalEpigraph φ ≤ ⊤)
    (W1p.normalEpigraphExtensionL hφ u)
  rw [W1p.restrictL_normalEpigraphExtensionL] at horiginal
  have habove := (ae_eq_restrict_iff_indicator_ae_eq
    (normalEpigraph φ).isOpen.measurableSet).mp horiginal.symm
  have hΦ := measurePreserving_graphFlattening φ φ.continuous
  have hρ := measurePreserving_normalReflection (E := E) 0
  have hwhole := gradient_unflattenWholeL_ae hφ (W1p.extendByReflectionL 0 v)
  rw [← normalEpigraphExtensionL_apply] at hwhole
  filter_upwards [habove, hwhole,
    hΦ.quasiMeasurePreserving.ae_eq_comp (W1p.gradient_extendByReflectionL_ae 0 v),
    hΦ.quasiMeasurePreserving.ae_eq_comp hflat,
    (hρ.comp hΦ).quasiMeasurePreserving.ae_eq_comp hflat] with x hu hx hreflect h1 h2
  by_cases hab : φ x.snd < x.fst
  · -- Above the graph, restriction already identifies the weak gradient.
    simpa only [Set.indicator_of_mem ((mem_normalEpigraph φ x).mpr hab), hab, ite_true] using hu
  · -- Below or on the graph, use the chain rule and the reflected half-space gradient.
    simp only [Function.comp_apply] at hreflect h1 h2
    rw [hx, hreflect, h1, h2]
    simp only [H, Φ, Set.indicator, SetLike.mem_coe, mem_normalHalfSpace,
      graphFlattening_apply, graphFlattening_symm_apply, normalReflection_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, mul_zero, zero_sub, neg_sub, sub_pos]
    have hheight : φ x.snd - x.fst + φ x.snd = 2 * φ x.snd - x.fst := by ring
    rw [hheight]
    by_cases hbelow : x.fst < φ x.snd <;>
      simp only [hab, hbelow, ite_true, ite_false, map_zero, zero_add, add_zero]

end TauCeti
end
end
