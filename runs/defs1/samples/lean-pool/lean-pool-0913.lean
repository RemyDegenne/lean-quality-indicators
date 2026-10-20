@[expose] public section

open Lean Parser Elab Term Meta Qq Std FirstOrder.Language

attribute [local implicit_reducible] 𝓛ZF

syntax "#" num : label

syntax "&" num : label

syntax "value_of_labels(" label,* ")" : term

syntax term "@(" label,* ")" : term

macro_rules
  | `($f:ident@($labels:label,*)) =>
    `(BoundedFormula.relabel
      value_of_labels($labels,*) $(mkIdent (f.getId ++ `formula)) (k := 0))
  | `(value_of_labels(#$n, $labels,*)) =>
    `(Matrix.vecCons (Sum.inl $n) value_of_labels($labels,*))
  | `(value_of_labels(&$n, $labels,*)) =>
    `(Matrix.vecCons (Sum.inr $n) value_of_labels($labels,*))
  | `(value_of_labels(#$n)) => `(Matrix.vecCons (Sum.inl $n) ![])
  | `(value_of_labels(&$n)) => `(Matrix.vecCons (Sum.inr $n) ![])
  | `(value_of_labels()) => `(Matrix.vecEmpty)

syntax (name := headBetaSyntax) "headBeta(" term ")" : term

syntax (name := exprSyntax) "expr(" strLit ")" : term

namespace BuildFormula

/-- The `simpFormula` declaration. -/
def simpFormula (e : Expr) : BuildFormulaM Expr := do
  let some ext ← getSimpExtension? `formula_builder | failure
  let ctx ← Simp.mkContext {} #[← ext.getTheorems]
  return (← simp e ctx).1.expr

end BuildFormula
end
