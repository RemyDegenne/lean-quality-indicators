namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

open scoped NNReal

namespace InvariantIsing

theorem fieldAffineValue_scalar (L : List FieldAffineStep) (t : ℝ) :
    (fun z => fieldAffineValue L (t, z)) =
      fieldScalarValue (fieldAffineIncrements L t) (fun z => Real.log (Real.cosh z)) := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    change gaussianTransform (av.base + av.slope * t) av.exponent
        (fun z => fieldAffineValue L (t, z)) = _
    rw [field_gaussianTransform_eq_operator, ih]
    rfl

end InvariantIsing
end
end OAI
