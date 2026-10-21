namespace OAI

universe uV uι

open MeasureTheory ProbabilityTheory

open scoped ENNReal

open scoped RealInnerProductSpace

open scoped RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal RealInnerProductSpace

open Filter

open scoped Topology

namespace GaussianPropeller.HeatConvolution

open GaussianPropeller.Stein

variable {ι : Type uι} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

local notation "γ" => stdGaussian E

section General

variable {V : Type uV} [NormedAddCommGroup V]

lemma continuous_heat [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {F : E → V} (hF : Continuous F) {B : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) : Continuous (fun p : ℝ × E => heat F p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ : E => B)
  · intro p; fun_prop
  · intro p; exact ae_of_all _ (fun z => hB _)
  · exact integrable_const _
  · filter_upwards [] with z; fun_prop

end General
end GaussianPropeller.HeatConvolution
end OAI
