@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})

theorem backward_naturality_right {M : PresheafOfModules.{v} R}
    {N N' : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)
    (ψ : N ⟶ N') :
    backward f R (h ≫ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).map ψ) =
      backward f R h ≫ ψ :=
  (homEquivCore f R).homEquiv_naturality_right_symm h ψ

end RingedSpaces.Modules.PresheafInverseImage
end
