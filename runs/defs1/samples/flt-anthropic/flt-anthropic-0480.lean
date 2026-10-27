namespace P2MW.S_AlgebraicCurve_exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg

set_option autoImplicit false

noncomputable section

p2m_open

open scoped Manifold ContDiff Topology

namespace AlgebraicCurve

namespace PrimitiveAlongRegularPathProof

p2m_open

section Surface

variable {F : Type*} [Field F] [Algebra ℂ F]

variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def ChartCompatible (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] : Prop :=
  ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)

end Surface
end PrimitiveAlongRegularPathProof
end AlgebraicCurve
end
end P2MW.S_AlgebraicCurve_exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg
