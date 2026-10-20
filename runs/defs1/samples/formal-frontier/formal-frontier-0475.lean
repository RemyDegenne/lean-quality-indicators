public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ConcreteCategory Opposite

open TopologicalSpace

universe u v

namespace SheafCohomology.CompactOpenSections

variable {X : Type u} [TopologicalSpace X]

variable {C : Type (v + 1)} [Category.{v} C]

variable {FC : C → C → Type*} {CC : C → Type v}

variable [∀ A B, FunLike (FC A B) (CC A) (CC B)]

variable [instCC : ConcreteCategory C FC] [HasColimitsOfSize.{v, v} C]

variable [HasLimitsOfSize.{u, u} C]

variable [PreservesFilteredColimits (forget C)]

variable [PreservesLimitsOfSize.{u, u} (forget C)]

variable [instReflectsIsomorphisms : (forget C).ReflectsIsomorphisms]

local notation "sections" => sectionsOf

variable [UnivLE.{u, v}]

variable [HasWeakSheafify
  (Opens.grothendieckTopology X) C]

variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  C]

variable {I : Type v} [SmallCategory I] [IsFiltered I]

variable (F : I ⥤ CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) C)

/-- The direct comparison from the colimit of sections to sections of the
explicit sheafification model. -/
@[expose] def explicitSectionsComparison (U : Opens X) :
    colimit (F ⋙ sections U) ⟶
      (sheafify (Opens.grothendieckTopology X)
        (underlyingPresheafColimit F)).obj (op U) :=
  (colimitObjIsoColimitCompEvaluation
      (F ⋙ CategoryTheory.sheafToPresheaf
        (Opens.grothendieckTopology X) C) (op U)).inv ≫
    (toSheafify (Opens.grothendieckTopology X)
      (underlyingPresheafColimit F)).app (op U)

end SheafCohomology.CompactOpenSections
end
end
