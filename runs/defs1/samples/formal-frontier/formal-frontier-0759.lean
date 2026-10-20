public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

namespace RationalPointSet

/-- Evaluation of global sections at a rational point. The codomain is transported from the
global sections of `Spec K` to `K` itself. -/
def eval {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (s : RationalPoint Y) : Γ(Y.left, ⊤) →+* K :=
  (s.1.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom

end RationalPointSet
end AlgebraicGeometry
end
end
