public section

noncomputable section

open CategoryTheory Limits unitInterval

universe u v₁ v₂ v₃ w

namespace TauCeti

namespace LocalCoefficientSystem

open SingularCube

open ContinuousMap (pathClass pathClass_self pathClass_comp_pathClass pathClass_comp map_pathClass)

variable {R : Type u} [Ring R] {X : TopCat.{v₁}} {Y : TopCat.{v₂}} {Z : TopCat.{v₃}}

namespace TwistedCubicalChain

section Augment

variable {L : LocalCoefficientSystem.{u, v₁, w} R X}

/-- The **augmentation** of the cubical `0`-chains into a cocone `s` over the local system: a
point `x` with a coefficient `a` goes to the image of `a` under the leg of `s` at `x`.  For the
colimit cocone it takes values in `colimit L`; for a constant system with fibre `M` and the cocone
of identities it is the sum of the coefficients. -/
def augment (s : Cocone L) : L.TwistedCubicalChain 0 →ₗ[R] s.pt :=
  desc L fun c ↦ (s.ι.app (FundamentalGroupoid.mk (c 0))).hom

end Augment
end TwistedCubicalChain
end LocalCoefficientSystem
end TauCeti
end
end
