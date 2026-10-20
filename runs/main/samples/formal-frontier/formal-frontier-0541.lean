@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

@[reassoc]
theorem twoOpenIntersectionToRight_comp {X : TopCat.{u}} (U V : Opens X) :
    twoOpenIntersectionToRight U V ≫ V.inclusion' = (U ⊓ V).inclusion' := by
  simpa [twoOpenIntersectionToRight] using
    TopCat.openMap_comp_inclusion (𝟙 X) (U ⊓ V) V (fun _ hx ↦ hx.2)

end AlgebraicTopology
end
end
