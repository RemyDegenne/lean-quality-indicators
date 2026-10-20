public section

noncomputable section

namespace MeasureTheory.Lp

open Module TauCeti TemperedDistribution TopologicalSpace

open scoped ENNReal LineDeriv SchwartzMap

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

theorem exists_real_lp_lineDeriv_of_memSobolev_zero {p : ENNReal} [Fact (1 ≤ p)]
    (u : Lp ℝ p (volume : Measure E)) (v : E)
    (h : MemSobolev 0 p
      (∂_{v} (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)))) :
    ∃ u' : Lp ℝ p (volume : Measure E),
      ∂_{v} (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) =
        Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u') := by
  obtain ⟨z, hz⟩ := memSobolev_zero_iff.mp h
  let u' : Lp ℝ p (volume : Measure E) := Complex.reCLM.compLp z
  refine ⟨u', ?_⟩
  apply TemperedDistribution.ext_real
  intro phi _
  have hderiv : ∀ x, ∂_{v} (phi.postcompCLM Complex.ofRealCLM) x =
      Complex.ofReal (lineDeriv ℝ (phi : E → ℝ) x v) := by
    intro x
    simp only [lineDerivOp_postcompCLM, SchwartzMap.postcompCLM_apply,
      Complex.ofRealCLM_apply, SchwartzMap.lineDerivOp_apply]
  have hzphi := congrArg
    (fun T : TemperedDistribution E ℂ => T (phi.postcompCLM Complex.ofRealCLM)) hz
  have hleft : ∂_{v} (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u))
      (phi.postcompCLM Complex.ofRealCLM) =
      Complex.ofReal (∫ x, -(lineDeriv ℝ (phi : E → ℝ) x v) * u x) := by
    simp only [TemperedDistribution.lineDerivOp_apply_apply,
      Lp.toTemperedDistribution_apply, neg_apply, hderiv]
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u] with x hx
    simp [hx]
  have hright : Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u')
      (phi.postcompCLM Complex.ofRealCLM) =
      Complex.ofReal (∫ x, (phi : E → ℝ) x * u' x) := by
    simp only [Lp.toTemperedDistribution_apply, SchwartzMap.postcompCLM_apply,
      Complex.ofRealCLM_apply]
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u'] with x hx
    simp [hx]
  rw [hleft, hright]
  apply congrArg Complex.ofReal
  have hzphi_re := congrArg Complex.re hzphi
  rw [hleft] at hzphi_re
  simp only [Complex.ofReal_re] at hzphi_re
  calc
    ∫ x, -(lineDeriv ℝ (phi : E → ℝ) x v) * u x =
        (Lp.toTemperedDistribution z (phi.postcompCLM Complex.ofRealCLM)).re := hzphi_re
    _ = ∫ x, (phi : E → ℝ) x * u' x := by
      simp only [Lp.toTemperedDistribution_apply, SchwartzMap.postcompCLM_apply,
        Complex.ofRealCLM_apply]
      let _ : ENNReal.HolderConjugate p (ENNReal.conjExponent p) :=
        ENNReal.HolderConjugate.conjExponent Fact.out
      have hint : Integrable (fun x => (phi x : ℂ) * z x) volume :=
        ((phi.postcompCLM Complex.ofRealCLM).memLp (ENNReal.conjExponent p)).integrable_mul
          (Lp.memLp z)
      simp only [smul_eq_mul]
      -- `Complex.re` is definitionally `RCLike.re` here; expose the latter spelling expected by
      -- `integral_re` before moving the real-part map through the integral.
      change RCLike.re (∫ x, (phi x : ℂ) * z x) = _
      rw [← integral_re hint]
      apply integral_congr_ae
      filter_upwards [Complex.reCLM.coeFn_compLp z] with x hx
      simp [u', hx]

end MeasureTheory.Lp
end
end
