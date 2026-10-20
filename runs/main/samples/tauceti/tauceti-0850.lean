public section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

noncomputable section

section LocallyNoetherian

variable [IsLocallyNoetherian X]

theorem isIso_unitToSheaf_zero (hX : ∀ y : X, coheight y ≤ 1) :
    IsIso (unitToSheaf (D := (0 : SchemeWeilDivisor X)) WeilDivisor.isEffective_zero) := by
  apply isIso_unitToSheaf WeilDivisor.isEffective_zero
  intro U t ht
  exact (mem_sections_zero_iff (fun y _ ↦ hX y) t).mp ht

end LocallyNoetherian
end
end SchemeWeilDivisor
end AlgebraicGeometry
end TauCeti
end
