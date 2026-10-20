public section

open MeasureTheory Set TauCeti.Probability SimpleGraph

namespace TauCeti

namespace DenseGraphLimits

@[fun_prop]
theorem measurable_graphOfArray : Measurable graphOfArray :=
  measurable_iff_adj.2 fun i j => by
    simp only [graphOfArray_adj]
    have hij : Measurable fun x : ℕ × ℕ → Bool => x (i, j) := measurable_pi_apply (i, j)
    have hji : Measurable fun x : ℕ × ℕ → Bool => x (j, i) := measurable_pi_apply (j, i)
    exact measurable_const.and ((hij.eq_const true).or (hji.eq_const true))

end DenseGraphLimits
end TauCeti
end
