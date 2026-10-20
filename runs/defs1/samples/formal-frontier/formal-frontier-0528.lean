@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- The pointwise Kan unit followed by the sheafification unit, as a sheaf map. -/
noncomputable def pointwiseSheafUnit (A : Type (v + 1)) [Category.{v} A]
    {FA : A → A → Type*} {CA : A → Type v}
    [∀ B C, FunLike (FA B C) (CA B) (CA C)] [ConcreteCategory.{v} A FA]
    [HasColimits A] [HasLimits A] [PreservesLimits (forget A)]
    [PreservesFilteredColimits (forget A)] [(forget A).ReflectsIsomorphisms]
    (S : Y.Sheaf A) :
    S ⟶ (TopCat.Sheaf.pushforward A f).obj
      ((presheafToSheaf (Opens.grothendieckTopology X) A).obj
        ((Opens.map f).op.pointwiseLeftKanExtension S.obj)) :=
  ⟨(Opens.map f).op.pointwiseLeftKanExtensionUnit S.obj ≫
    (Opens.map f).op.whiskerLeft
      (toSheafify (Opens.grothendieckTopology X)
        ((Opens.map f).op.pointwiseLeftKanExtension S.obj))⟩

end RingedSpaces.Modules.SheafInverseImage
end
