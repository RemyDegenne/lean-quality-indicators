@[expose] public section

universe u v w

namespace Valuation

variable {K : Type u} [Field K] {ι : Type v} {Γ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] (val : ι → Valuation K Γ₀)

theorem intersectionResidueProduct_ext {x y : intersectionSubring val}
    (h : ∀ i, intersectionResidueMap val i x = intersectionResidueMap val i y) :
    intersectionResidueProduct val x = intersectionResidueProduct val y :=
  funext fun i => h i

end Valuation
end
