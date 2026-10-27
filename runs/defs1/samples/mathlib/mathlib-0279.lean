@[expose] public section

open Function Set NNReal

variable {α : Type*}

@[inherit_doc]
scoped[ENNReal] notation "ℝ≥0∞" => ENNReal

scoped[ENNReal] notation3 "∞" => (⊤ : ENNReal)

open ENNReal

namespace Mathlib.Meta.Positivity

open Lean Qq

/-- Extension for the `positivity` tactic: `ENNReal.ofNNReal`. -/
@[positivity ENNReal.ofNNReal _]
meta def evalENNRealOfNNReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ≥0∞), ~q(ENNReal.ofNNReal $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure <| .positive q(ENNReal.coe_pos.mpr $pa)
    | _ => pure .none
  | _, _, _ => throwError

end Mathlib.Meta.Positivity
end
