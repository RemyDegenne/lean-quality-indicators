namespace OAI

noncomputable section

open scoped ComplexConjugate

open scoped BigOperators

open scoped BigOperators BoundedContinuousFunction

open Filter Topology

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate

open scoped BigOperators

open scoped BigOperators

open Polynomial

open MeasureTheory

open scoped BigOperators

open MeasureTheory

open scoped BigOperators

open MeasureTheory

open MeasureTheory ProbabilityTheory

open scoped BigOperators

open MeasureTheory

open scoped BigOperators ComplexConjugate

open MeasureTheory ProbabilityTheory

open scoped ENNReal BigOperators

open MeasureTheory Filter

open scoped Topology ENNReal NNReal

namespace EuclideanFiveColor.CosetCenter

open ProbabilityTheory

variable {G : Type*} [CommGroup G] [MeasurableSpace G]

namespace Embedding

variable (e : Embedding G)

variable [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem coset_mul_j (z : G) (v : ℂ) : e.coset (z * e.j v) = e.coset z := by
  ext d
  have hj : e.j v ∈ e.ordinary := ⟨_, rfl⟩
  constructor
  · intro h
    change d / z ∈ e.ordinary
    convert e.ordinary.mul_mem h hj using 1
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  · intro h
    change d / (z * e.j v) ∈ e.ordinary
    convert e.ordinary.div_mem h hj using 1
    simp [div_eq_mul_inv, mul_assoc, mul_comm]

end Embedding
end EuclideanFiveColor.CosetCenter
end
end OAI
