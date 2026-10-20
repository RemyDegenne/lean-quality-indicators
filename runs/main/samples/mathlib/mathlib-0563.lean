@[expose] public section

open Set Function MeasureTheory MeasureTheory.Measure TopologicalSpace AddSubgroup intervalIntegral

open scoped MeasureTheory NNReal ENNReal

namespace UnitAddCircle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

protected theorem integral_preimage (t : ℝ) (f : UnitAddCircle → E) :
    (∫ a in Ioc t (t + 1), f a) = ∫ b : UnitAddCircle, f b :=
  AddCircle.integral_preimage 1 t f

end UnitAddCircle
end
