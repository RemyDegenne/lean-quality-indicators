public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

namespace FieldValuedPoints

/-- Evaluation of global sections at an extension-field-valued point. The codomain is transported
from the global sections of `Spec L` to `L` itself. -/
def eval {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} (p : FieldValuedPoint (L := L) Y) :
    Γ(Y.left, ⊤) →+* L :=
  (p.1.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom

end FieldValuedPoints
end AlgebraicGeometry
end
end
