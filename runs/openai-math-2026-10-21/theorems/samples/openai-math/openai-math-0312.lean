namespace OAI

noncomputable section

namespace ScalarConductivity

section

open Set MeasureTheory Filter Topology UnitAddTorus

open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma finiteDecayLp_angular_bound (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (h : TorusModes) (j : Fin 2) (a : ℂ) :
    ‖finiteDecayLp (torusRate s h) R (Complex.I*(h j:ℂ)*a)‖^2 ≤
      2*torusRate s h*‖a‖^2 := by
  have hr := finiteDecayLp_rate_norm_sq (torusRate s h) R (Real.sqrt_nonneg _) a
  rw [finiteDecayLp_real_norm_sq] at hr
  have hh := mul_le_mul_of_nonneg_right (torusFrequency_sq_le_rate s hs h j)
    (sq_nonneg ‖finiteDecayLp (torusRate s h) R a‖)
  have he : (h j:ℂ)=((h j:ℝ):ℂ) := by norm_cast
  rw [he,finiteDecayLp_imag_norm_sq]
  nlinarith only [hr,hh]

end
end ScalarConductivity
end
end OAI
