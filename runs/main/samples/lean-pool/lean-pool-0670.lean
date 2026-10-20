@[expose] public section

namespace NRR

open scoped BigOperators

namespace AffinePositiveRayBoundary

variable {p : Nat}

namespace VertexMap

theorem lowerEndpoint_unique_zero_of_positiveMean
    (hp : Nat.Prime p) (V : VertexMap p)
    (hregular : FacetRegular hp V)
    (hcodim : AvoidsPositiveRayCodimTwo hp V)
    (w : StandardSimplex p)
    (hw : ∀ q : Fin (p - 1), deviation hp (affineValue V w) q = 0)
    (hmean : 0 < mean p
      (affineValue V (lineSimplexPoint hp V w
        (lowerParameter hp V hregular w)
        (lowerParameter_feasible hp V hregular w))))
    (j : Fin (p + 1))
    (hj : lineCoordinate hp V w (lowerParameter hp V hregular w) j = 0) :
    j = lowerEndpointIndex hp V hregular w := by
  by_contra hne
  let ht := lowerParameter_feasible hp V hregular w
  let wLower := lineSimplexPoint hp V w (lowerParameter hp V hregular w) ht
  have hdev : ∀ q : Fin (p - 1),
      deviation hp (affineValue V wLower) q = 0 := by
    intro q
    exact lineSimplexPoint_deviation_eq_zero hp V w hw _ ht q
  exact hcodim wLower j (lowerEndpointIndex hp V hregular w) hne hdev
    (by simpa [wLower] using hmean)
    ⟨by simpa [wLower] using hj,
      by simpa [wLower] using lowerEndpoint_coordinate_eq_zero hp V hregular w⟩

end VertexMap
end AffinePositiveRayBoundary
end NRR
end
