namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron Set

namespace InvariantIsing

lemma restrictedSpinKernel_univ (N : ℕ) :
    restrictedSpinKernel (Finset.univ : Finset (Spin N)) = fieldVectorSpinKernel N := by
  ext z : 1
  change cond (fieldVectorSpinKernel N z) (Finset.univ : Finset (Spin N)) = _
  simpa only [Finset.coe_univ] using (cond_univ (μ := fieldVectorSpinKernel N z))

end InvariantIsing
end
end OAI
