public section

namespace TauCeti

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {S S' : C} (p : S' ⟶ S)

/-- A descent datum on `X : Over S'` relative to `p : S' ⟶ S`, in action form: a morphism
`act : S' ×_S X ⟶ X`, `(s, x) ↦ s · x`, with `π (s · x) = s`, `π x · x = x` and
`s₁ · (s₂ · x) = s₁ · x`, where `π = X.hom`. -/
@[ext]
structure DescentDatum (X : Over S') where
  /-- The action `S' ×_S X ⟶ X`, `(s, x) ↦ s · x`. -/
  act : pullback p (X.hom ≫ p) ⟶ X.left
  /-- The action moves `x` into the fibre over `s`: `π (s · x) = s`. -/
  act_hom : act ≫ X.hom = pullback.fst p (X.hom ≫ p)
  /-- Normalisation: `π x · x = x`. -/
  lift_act : pullback.lift X.hom (𝟙 X.left) (by simp) ≫ act = 𝟙 X.left
  /-- The cocycle condition: `s₁ · (s₂ · x) = s₁ · x` on `S' ×_S (S' ×_S X)`. -/
  act_assoc :
    pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
        (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ act)
        (by rw [Category.assoc, reassoc_of% act_hom]; exact pullback.condition) ≫ act =
      pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
        (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ pullback.snd p (X.hom ≫ p))
        (by
          rw [Category.assoc, ← pullback.condition (f := p) (g := X.hom ≫ p)]
          exact pullback.condition) ≫ act

end TauCeti
end
