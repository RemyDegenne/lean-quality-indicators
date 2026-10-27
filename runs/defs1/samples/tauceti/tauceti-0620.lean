public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory.ExactPairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The right adjoint mate `Y' ⟶ X'` of `f : X ⟶ Y`, with respect to explicitly given exact
pairings `(X, X')` and `(Y, Y')`: Mathlib's `CategoryTheory.rightAdjointMate` with the given
pairings made ambient. Stating it with the type `Y' ⟶ X'` keeps the duals `X'` and `Y'` visible
to rewriting: as a term `@rightAdjointMate C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f`, its source and target are the
projections `HasRightDual.rightDual ⟨Y'⟩` and `HasRightDual.rightDual ⟨X'⟩`, and Mathlib's lemmas
about it do not rewrite against the evaluation `ε_ X X'` of the given pairing. -/
def rightMate {X X' Y Y' : C} (pX : ExactPairing X X') (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    Y' ⟶ X' :=
  @rightAdjointMate C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f

end CategoryTheory.ExactPairing
end
