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

section Basic

variable (L : LocalCoefficientSystem.{u, v₁, w} R X)

variable {L}

open scoped Classical in
@[elab_as_elim]
theorem induction_on {n : ℕ} {P : L.TwistedCubicalChain n → Prop} (x : L.TwistedCubicalChain n)
    (zero : P 0)
    (ofCube : ∀ c a, P (ofCube L c a)) (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  refine DirectSum.induction_on x zero (fun c a ↦ ?_) add
  have hc := ofCube c a
  rwa [TwistedCubicalChain.ofCube] at hc

end Basic
end TwistedCubicalChain
end LocalCoefficientSystem
end TauCeti
end
end
