namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixAlignment

open StatementCircuit CircuitBatch PostfixModel

variable {ι : Type*}

@[simp] theorem forestTokens_cons (wire : ι → Nat) (e : Expr ι) (es : List (Expr ι)) :
    forestTokens wire (e :: es) = exprTokens wire e ++ forestTokens wire es := rfl

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixAlignment
end
end OAI
