public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

namespace FieldValuedPoints

/-- An extension-field-valued point gives a rational point after scalar extension by the universal
property of the pullback. -/
def toBaseChangeRationalPoint {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} (p : FieldValuedPoint (L := L) Y) :
    RationalPoint (baseChange (L := L) Y) :=
  ⟨pullback.lift p.1 (𝟙 _)
      (by simpa using p.2), by
    exact pullback.lift_snd _ _ _⟩

end FieldValuedPoints
end AlgebraicGeometry
end
end
