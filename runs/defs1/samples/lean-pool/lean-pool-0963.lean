@[expose] public section

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-- Finite pointed-model existence: every locally consistent theory presented
by a list has a model, valuation, and point matching all its members. -/
def FiniteLocalModelExistence (S : Signature) (Var : Type) [DecidableEq Var] : Prop :=
  ∀ l : List (Pattern S Var), LocConsistent {delta | delta ∈ l} →
    ∃ (M : Model S) (rho : Var → M.carrier) (u : M.carrier),
      u ∈ M.denoteSet rho {delta | delta ∈ l}

end MatchingLogic
end
