namespace OAI

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

open scoped BigOperators ComplexConjugate

open MeasureTheory ProbabilityTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

open MeasureTheory ProbabilityTheory Real Complex

open scoped ENNReal ComplexConjugate

open ProbabilityTheory

open MeasureTheory Filter Set

open scoped ENNReal Topology

open MeasureTheory Set

open scoped ENNReal

namespace HardSphere

open MeasureTheory Set Filter

open scoped ComplexConjugate

variable {n : ℕ} [Nontrivial (Fin n)]

lemma closeHighProfile_deriv_zero {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t∉Icc h (2*h)) :
    deriv (closeHighProfile h) t=0 := by
  rw [closeHighProfile_deriv,CellOrbital.profile_deriv_zero hh ht,neg_zero]

end HardSphere
end
end OAI
