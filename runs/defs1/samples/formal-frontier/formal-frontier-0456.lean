@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})

/-- The actual neighborhood-colimit inverse-image functor is left adjoint to native pushforward. -/
noncomputable def adjunction : inverseImageFunctor f R ⊣
    PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv f R
      homEquiv_naturality_left_symm := by
        intro M' M N φ h
        apply (homEquiv f R M' N).injective
        change forward f R (backward f R (φ ≫ h)) = forward f R
          ((inverseImageFunctor f R).map φ ≫ backward f R h)
        rw [forward_backward f R (φ ≫ h), forward_naturality_left f R φ,
          forward_backward f R h]
      homEquiv_naturality_right := by
        intro M N N' g ψ
        exact forward_naturality_right f R g ψ }

end RingedSpaces.Modules.PresheafInverseImage
end
