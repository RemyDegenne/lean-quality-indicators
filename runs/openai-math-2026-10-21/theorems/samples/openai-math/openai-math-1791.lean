namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage

open Finset

namespace Input

theorem client_ne_facility (C : Input) (j : Fin C.m) (i : Fin C.n) :
    C.client j ≠ C.facility i := by
  intro h
  have hh := finSumFinEquiv.injective h
  cases hh

end Input
end MetricKMedian.Coverage
end Inline_PCPInherited
end OAI
