@[expose] public section

universe v' v u

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasProducts.{v'} C]

variable {X : TopCat.{v'}} (F : Presheaf C X) {ι : Type v'} (U : ι → Opens X)

namespace Presheaf

/-- The sheaf condition for a `F : Presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ᶜ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ᶜ F.obj (U i) ⟶ ∏ᶜ F.obj (U i) ⊓ (U j)`.
-/
def IsSheafEqualizerProducts (F : Presheaf.{v', v, u} C X) : Prop :=
  ∀ ⦃ι : Type v'⦄ (U : ι → Opens X), Nonempty (IsLimit (SheafConditionEqualizerProducts.fork F U))

end Presheaf
end TopCat
end
end
