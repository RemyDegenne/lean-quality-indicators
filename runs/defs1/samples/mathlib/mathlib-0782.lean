public meta section

namespace CategoryTheory

open Lean Elab Term Meta PrettyPrinter Delaborator SubExpr

namespace OfNotation

/-- The number of explicit arguments of a declaration of type `ty`, together with the index of the
last one among *all* of its arguments.

Metadata is ignored. Returns `none` if `ty` takes no explicit argument. -/
def explicitArgs? (ty : Expr) : Option (Nat × Nat) := go ty 0 0 none where
  /-- Walk down the binders of `ty`, where `idx` is the index of the current argument, `num` the
  number of explicit arguments seen so far and `lastIdx?` the index of the last one. -/
  go : Expr → Nat → Nat → Option Nat → Option (Nat × Nat)
    | .mdata _ ty, idx, num, lastIdx? => go ty idx num lastIdx?
    | .forallE _ _ body bi, idx, num, lastIdx? =>
      if bi.isExplicit then go body (idx + 1) (num + 1) (some idx)
      else go body (idx + 1) num lastIdx?
    | _, _, num, lastIdx? => lastIdx?.map (num, ·)

end OfNotation
end CategoryTheory
end
