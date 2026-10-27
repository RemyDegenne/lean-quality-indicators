@[expose] public section

open Lean Parser Elab Term Meta Qq Std FirstOrder.Language

namespace BuildFormula

/-- The `realizedTerm` declaration. -/
def realizedTerm (typeLetter := "M") : BuildFormulaM Term := do
  let realizedIdent := mkIdent' (← name)
  if (← numFreeVars) == 0 then
    let n ← forallTelescopeReducing
      ((← getEnv).find? (← name) |>.get! |>.type)
      fun vars _ => pure vars.size
    return Syntax.mkApp (← `(@$realizedIdent)) <|
      #[(mkIdent typeLetter.toName : Term)] ++ Array.replicate (n - 1) (← `(_))
  else
    `($realizedIdent)

end BuildFormula
end
