public section

open CategoryTheory

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C]

/-- **The opposite-handed successor isomorphism `e ^ (j + 1) ≅ e ^ j ⋙ e`.** -/
def _root_.CategoryTheory.Equivalence.powSuccRightIso (e : C ≌ C) (j : ℤ) :
    (e ^ (j + 1)).functor ≅ (e ^ j).functor ⋙ e.functor :=
  e.powAddIso j 1

end TauCeti
end
