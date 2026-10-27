public section

namespace TopRep

open CategoryTheory

variable {R : Type*} [Ring R] [TopologicalSpace R]
  {G : Type*} [Monoid G] {X Y Z : TopRep R G}

/-- The projection from a representation to its quotient by an invariant submodule. -/
def quotientπ (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) : X ⟶ quotient X W hW :=
  ofHom
    { toContinuousLinearMap := W.mkQL
      isIntertwining' g := by
        ext x
        simp [ContRepresentation.quotient_apply_mk] }

end TopRep
end
