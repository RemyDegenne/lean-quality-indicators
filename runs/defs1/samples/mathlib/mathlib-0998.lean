@[expose] public section

open Ordinal Order

namespace ONote

/-- Comparison of ordinal notations:

`ω ^ e₁ * n₁ + a₁` is less than `ω ^ e₂ * n₂ + a₂` when either `e₁ < e₂`, or `e₁ = e₂` and
`n₁ < n₂`, or `e₁ = e₂`, `n₁ = n₂`, and `a₁ < a₂`. -/
def cmp : ONote → ONote → Ordering
  | 0, 0 => Ordering.eq
  | _, 0 => Ordering.gt
  | 0, _ => Ordering.lt
  | _o₁@(oadd e₁ n₁ a₁), _o₂@(oadd e₂ n₂ a₂) =>
    (cmp e₁ e₂).then <| (_root_.cmp (n₁ : ℕ) n₂).then (cmp a₁ a₂)

end ONote
end
