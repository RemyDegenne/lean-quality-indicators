public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

namespace FieldValuedPoints

/-- Points of a scheme valued in an extension field are equivalent to rational points of its base
change to that field. -/
def fieldValuedPointEquivRationalPointBaseChange
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} :
    FieldValuedPoint (L := L) Y ≃ RationalPoint (baseChange (L := L) Y) where
  toFun := toBaseChangeRationalPoint
  invFun := ofBaseChangeRationalPoint
  left_inv p := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
  right_inv q := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · dsimp only [toBaseChangeRationalPoint]
      rw [pullback.lift_snd]
      simpa [baseChange] using q.2.symm

end FieldValuedPoints
end AlgebraicGeometry
end
end
