@[expose] public section

noncomputable section

open Filter Set

open scoped Topology

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `π` is always positive. -/
@[positivity Real.pi]
meta def evalRealPi : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.pi) =>
    assertInstancesCommute
    pure (.positive q(Real.pi_pos))
  | _, _, _ => throwError

end Mathlib.Meta.Positivity
end
end
