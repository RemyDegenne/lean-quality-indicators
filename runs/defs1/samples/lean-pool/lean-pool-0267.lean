@[expose] public section

namespace MeasureTheory

open scoped ENNReal

namespace Lp

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The identity map as a linear map `Lp E p μ →ₗ[ℝ] Lp E p ν` under a measure bound `ν ≤ c • μ`. -/
noncomputable def changeMeasureₗ {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • μ) :
    Lp E p μ →ₗ[ℝ] Lp E p ν where
  toFun := changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν
  map_add' f g := by
    classical
    refine MeasureTheory.Lp.ext ?_
    have habs : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
    have haddμ : ⇑(f + g) =ᵐ[ν] (f + g) :=
      habs.ae_le (by
        exact (MeasureTheory.Lp.coeFn_add (μ := μ) f g))
    filter_upwards
      [ changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc hν (f + g)
      , changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc hν f
      , changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc hν g
      , haddμ
      , MeasureTheory.Lp.coeFn_add
          (μ := ν)
          (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f)
          (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν g)
      ] with x hfg hf hg haddμ hadd
    have hadd' :
        (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x +
            (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν g) x =
          (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f +
              changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν g) x := by
      simpa [Pi.add_apply] using hadd.symm
    calc
      changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν (f + g) x = (f + g) x := by
            simpa using hfg
      _ = f x + g x := by
            simpa [Pi.add_apply] using haddμ
      _ = (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x +
            (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν g) x := by
            simp [hf, hg]
      _ = (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f +
            changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν g) x := hadd'
  map_smul' r f := by
    classical
    refine MeasureTheory.Lp.ext ?_
    have habs : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
    have hsmulμ : ⇑(r • f) =ᵐ[ν] (r • (f : α → E)) :=
      habs.ae_le (by
        exact (MeasureTheory.Lp.coeFn_smul (μ := μ) r f))
    filter_upwards
      [ changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc hν (r • f)
      , changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc hν f
      , hsmulμ
      , MeasureTheory.Lp.coeFn_smul (μ := ν) r (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f)
      ] with x hrf hf hsmulμ hsmul
    have hsmul' :
        r • (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x =
          (r • changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x := by
      simpa [Pi.smul_apply] using hsmul.symm
    calc
      changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν (r • f) x = (r • f) x := by
            simpa using hrf
      _ = r • f x := by
            simpa [Pi.smul_apply] using hsmulμ
      _ = r • (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x := by
            simp [hf]
      _ = (r • changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x := hsmul'

end
end Lp
end MeasureTheory
end
