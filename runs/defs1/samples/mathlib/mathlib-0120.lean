public meta section

open scoped Bundle Manifold ContDiff

open Lean Meta Elab Tactic

open Mathlib.Tactic

open Qq

section delaborators

namespace Manifold

open Bundle PrettyPrinter Delaborator SubExpr

/-- Delaborator for `HasMFDerivWithinAt` using the custom elaborator -/
@[app_delab HasMFDerivWithinAt] meta def delabHasMFDerivWithinAt : Delab := do
  whenPPOption getPPNotation do
  withOverApp 24 do
  let ss ← withNaryArg 21 delab
  let xs ← withNaryArg 22 delab
  let f' ← withNaryArg 23 delab
  let fs ← withNaryArg 20 delab
  `(HasMFDerivAt[$ss] $fs $xs $f') >>= annotateGoToSyntaxDef

end Manifold
end delaborators
end
