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

omit [IsFiltered I] [UnivLE.{u, v}]
  [HasLimitsOfSize.{u, u} C]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    C] in
@[reassoc]
theorem colimit_ι_explicitSectionsComparison (U : Opens X) (i : I) :
    colimit.ι
          ((F ⋙ CategoryTheory.sheafToPresheaf
              (Opens.grothendieckTopology X) C) ⋙
            (evaluation (Opens X)ᵒᵖ C).obj (op U)) i ≫
        (colimitObjIsoColimitCompEvaluation
          (F ⋙ CategoryTheory.sheafToPresheaf
            (Opens.grothendieckTopology X) C) (op U)).inv ≫
        (toSheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).app (op U) =
      ((explicitSheafColimitCocone F).ι.app i).hom.app (op U) := by
  rw [← Category.assoc, colimitObjIsoColimitCompEvaluation_ι_inv]
  exact NatTrans.congr_app
    (CategoryTheory.Sheaf.sheafifyCocone_ι_app_val
      (colimit.cocone
        (F ⋙ CategoryTheory.sheafToPresheaf
          (Opens.grothendieckTopology X) C)) i)
    (op U) |>.symm

end SheafCohomology.CompactOpenSections
end
end
