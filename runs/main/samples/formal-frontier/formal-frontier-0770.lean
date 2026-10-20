@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})

theorem backward_naturality_left {M' M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (φ : M' ⟶ M)
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) :
    backward f R (φ ≫ h) =
      (inverseImageFunctor f R).map φ ≫ backward f R h :=
  (homEquivCore f R).homEquiv_naturality_left_symm φ h

end RingedSpaces.Modules.PresheafInverseImage
end
