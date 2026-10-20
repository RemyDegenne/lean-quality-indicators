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

section Map

variable (f : C(X, Y)) (L : LocalCoefficientSystem.{u, v₂, w} R Y)

/-- The map of cubical chains induced by a continuous map `f`, from the chains with coefficients
in the pulled back system `f⁎L` to the chains with coefficients in `L`. -/
-- The summand of a cube `c` in the source, `L.obj ⟨f (c 0)⟩`, is definitionally the summand of
-- the cube `f.comp c` in the target.
def map (n : ℕ) : ((pullback f).obj L).TwistedCubicalChain n →ₗ[R] L.TwistedCubicalChain n :=
  desc _ fun c ↦ ofCube L (f.comp c)

end Map
end TwistedCubicalChain
end LocalCoefficientSystem
end TauCeti
end
end
