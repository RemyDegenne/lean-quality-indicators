public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

section BaseChange

variable (S : ShortComplex C) {Z' Q : C} {u : Z' ⟶ S.X₃} {v : Q ⟶ S.X₂} {w : Q ⟶ Z'}

/-- The morphism `S.X₁ ⟶ Q` into a base change of `S.g` along `u`, induced by `S.f` on the one
factor and by `0` on the other. -/
noncomputable def baseChangeι (sq : IsPullback v w S.g u) : S.X₁ ⟶ Q :=
  sq.lift S.f 0 (by simp [S.zero])

end BaseChange
end TauCeti
end
