public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Complex Filter

open scoped Topology

variable {μ ν : Measure ℝ}

theorem Measure.ext_of_forall_integral_pow_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
    (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν)) (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    μ = ν :=
  Measure.ext_of_charFun (charFun_eq_of_forall_integral_pow_eq hμ hν hmom)

end TauCeti
end
