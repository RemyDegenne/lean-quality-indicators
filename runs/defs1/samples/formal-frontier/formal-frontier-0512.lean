@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- The pointwise scalar operation, with its module instance explicitly selected. -/
noncomputable def pointwiseSmul (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
    (m : ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :
    ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U) := by
  letI := pointwiseModule f R M U
  exact r • m

end RingedSpaces.Modules.PresheafInverseImage
end
