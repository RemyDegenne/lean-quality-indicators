public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

namespace RationalPointSet

theorem schematicallyDense_iff_isReduced_and_dense
    {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) :
    SchematicallyDense S ↔ IsReduced Y.left ∧ Dense (underlyingPoints S) := by
  let _ (s : S) : QuasiCompact s.1.1 := quasiCompact s.1
  let _ (s : S) : IsReduced (Spec (.of K)) := inferInstance
  exact jointlySchemeTheoreticallyDominant_iff_isReduced_and_denseRange
    (fun s : S ↦ s.1.1)

end RationalPointSet
end AlgebraicGeometry
end
end
