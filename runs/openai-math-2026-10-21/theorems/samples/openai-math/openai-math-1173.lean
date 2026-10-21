namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

namespace AggregationSpace

open UniformSpace VariableExponent

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

theorem sixth_supported (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x z : AggregationSpace T e) {H : Finset ι} (hH : T.Initial H)
    (hx : projection T e H hH x = x) (hz : z ∈ tail T e H hH) :
    sixthConstant * ‖z‖ ^ 6 ≤
      (‖x+z‖^2 + ‖x-z‖^2 - 2*‖x‖^2) * (‖x+z‖^2 + ‖x-z‖^2)^2 := by
  have hh := norm_lens_average T e x z
  exact sixth_of_cubic (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hh.1 hh.2 (cubic_supported T e h he hstep hheight x z hH hx hz)

end AggregationSpace
end RecursivePotentials
end
end OAI
