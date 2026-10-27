@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- Ordinary inverse image as a functor on presheaves of modules. -/
noncomputable def inverseImageFunctor (R : Y.Presheaf RingCat.{v}) :
    PresheafOfModules.{v} R ⥤
      PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R) where
  obj M := inverseImageModule f R M
  map φ := inverseImageMap f φ
  map_id M := by
    apply (PresheafOfModules.toPresheaf _).map_injective
    exact pointwiseMap_id f R M
  map_comp φ ψ := by
    apply (PresheafOfModules.toPresheaf _).map_injective
    exact pointwiseMap_comp f R φ ψ

end RingedSpaces.Modules.PresheafInverseImage
end
