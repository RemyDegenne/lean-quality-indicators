@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace SpectralStoneDuality.FiniteCoordinates

variable {X : Type u} [TopologicalSpace X]

/-- The compatible-family cone is limiting for any topological space. -/
noncomputable def familyConeIsLimit (X : Type u) [TopologicalSpace X] :
    IsLimit (familyCone X) := by
  refine ⟨familyLift, familyLift_fac, ?_⟩
  intro c m hm
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Family.ext
  intro F
  have h := congrArg
    (fun f : c.pt ⟶ (stageDiagram X).obj (Opposite.op F) => f x)
    (hm (Opposite.op F))
  exact h

end SpectralStoneDuality.FiniteCoordinates
end
