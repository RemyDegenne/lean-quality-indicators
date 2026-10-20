@[expose] public section

universe w'' w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace PreOneHypercover

variable {S : C} {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S}

variable [Limits.HasPullbacks C] (f g : E.Hom F)

/-- (Implementation): The covering object of `cylinder f g`. -/
noncomputable
abbrev cylinderX {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : C :=
  pullback (pullback.lift (f.h₀ i) (g.h₀ i) (by simp)) (F.toPullback k)

end PreOneHypercover
end CategoryTheory
end
