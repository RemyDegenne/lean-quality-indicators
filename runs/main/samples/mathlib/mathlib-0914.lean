open Filter Finset

variable {R : Type*} [NormedCommRing R] [NormOneClass R]

public section

variable [CompleteSpace R]

theorem hasSum_eulerFunction_pentagonal {x : R} (hx : ‖x‖ < 1) :
    HasSum (fun k ↦ k.negOnePow * x ^ pentagonal k) (eulerFunction x) := by
  simpa [pentagonal_injective, PowerSeries.coeff_pentagonalSeries_mul_eq_extend] using
    hasSum_eulerFunction_pentagonalSeries hx

end
