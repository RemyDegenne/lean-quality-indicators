public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

open scoped Set.Notation

universe u v

noncomputable section

namespace SpectralStoneDuality

variable {J : Type v} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u}) (i : J)

theorem chosenLimitCylinder_subset_iff_eventually
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {a b : J} (f : a ⟶ b), IsSpectralMap (F.map f))
    [HasLimit F]
    (U V : Set (F.obj i)) (hUopen : IsOpen U) (hUcompact : IsCompact U)
    (hVopen : IsOpen V) :
    (limit.π F i) ⁻¹' U ⊆ (limit.π F i) ⁻¹' V ↔
      ∃ X : Over i, F.map X.hom ⁻¹' U ⊆ F.map X.hom ⁻¹' V := by
  exact limitCylinder_subset_iff_eventually F i hX hmap
    (limit.cone F) (limit.isLimit F) U V hUopen hUcompact hVopen

end SpectralStoneDuality
end
end
