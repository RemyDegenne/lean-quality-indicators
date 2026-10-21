namespace OAI

noncomputable section

namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Filter Set

open scoped Classical ENNReal NNReal BigOperators Topology

lemma indexedShiftSum_zero {X S : Type} [MeasurableSpace S] (step : X×S → X)
    (n : ℕ) (p : X×IndexedCascadeMarks S n) (l : IndexedLeaf n) :
    indexedShiftSum step n (fun _ _ => 0) p l = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [indexedShiftSum, ih, add_zero]

end SphericalPerceptronFreeEnergy
end
end OAI
