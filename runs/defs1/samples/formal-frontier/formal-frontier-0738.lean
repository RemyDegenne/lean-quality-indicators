public section

open CategoryTheory Limits

open CategoryTheory.MonoidalCategory CartesianMonoidalCategory MonObj

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {G : Scheme.{u}}

/-- Over an algebraically closed field, the group-scheme-valued points are in
bijection with the closed points, as in Milne, *Algebraic Groups* (2017),
item 1.7, using Mathlib's `pointEquivClosedPoint`. -/
@[expose]
def groupSchemePointEquivClosedPoint (f : G ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [IsAlgClosed K] :
    (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) ≃ closedPoints G :=
  (groupSchemePointEquiv f).trans (pointEquivClosedPoint f)

end AlgebraicGeometry
end
end
