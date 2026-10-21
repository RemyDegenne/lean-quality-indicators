namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder

open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma bridgeListLaw_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (H : ℕ)
    (hH : Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) ≠ 0) :
    IsProbabilityMeasure (bridgeListLaw ν L H) := by
  constructor
  rw [bridgeListLaw,Measure.smul_apply,smul_eq_mul,bridgeListMeasure_mass,
    ENNReal.inv_mul_cancel hH (measure_ne_top _ _)]

end DirectionalZeroOne
end OAI
