namespace OAI

open MeasureTheory Set

open scoped ENNReal BigOperators

namespace StandardMapEntropy

open scoped Matrix.Norms.Operator

open Filter

open scoped Topology

open Metric

section

lemma iteratedDeriv_rescaledPotential (k q₀ θ L h : ℝ) (j p : ℕ) (hp : p ≤ 4) :
    iteratedDeriv p (fun x => potential k (rescaledOrbit k q₀ θ L x j)) h =
      rescaledPotentialJet p k q₀ θ L h j := by
  apply iteratedDeriv_of_jets univ isOpen_univ (fun p h => rescaledPotentialJet p k q₀ θ L h j) 4 _ p hp h (mem_univ _)
  intro i hi x _
  interval_cases i
  · exact hasDerivAt_rescaledPotential k q₀ θ L x j
  · exact hasDerivAt_rescaledV₁ k q₀ θ L x j
  · exact hasDerivAt_rescaledV₂ k q₀ θ L x j
  · exact hasDerivAt_rescaledV₃ k q₀ θ L x j

end
end StandardMapEntropy
end OAI
