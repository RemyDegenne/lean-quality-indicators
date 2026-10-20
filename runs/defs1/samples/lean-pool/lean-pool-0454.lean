@[expose] public section

namespace Connes

namespace CrossedProduct

open MeasureTheory

open scoped NNReal ENNReal

noncomputable section

universe u v w x

/-- The crossed-product group unitary on the indexed Hilbert space.
Paper: §3.
-/
def crossedGroupUnitary
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) (k : K) :
    crossedHilbert X ≃ₗᵢ[ℂ] crossedHilbert X :=
  (crossedIndexEquiv (Equiv.mulLeft k)).trans
    (crossedFiberwiseEquiv (crossedActionL2Equiv X k))

end
end CrossedProduct
end Connes
end
