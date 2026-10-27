@[expose] public section

universe v

open CategoryTheory

namespace SimplexCategory

scoped[Simplicial] notation "⦋" n "⦌" => SimplexCategory.mk n

open Simplicial

namespace Truncated

scoped macro "trunc" : tactic =>
  `(tactic| first | assumption | dsimp only [SimplexCategory.len_mk] <;> lia)

open Mathlib.Tactic (subscriptTerm) in
scoped syntax:max (name := mkNotation)
  "⦋" term ("," term)? "⦌" noWs subscriptTerm : term

scoped macro_rules
  | `(⦋$m:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, by first | trunc |
      fail "Failed to prove truncation property. Try writing `⦋m, by ...⦌ₙ`."⟩ :
      SimplexCategory.Truncated $n))
  | `(⦋$m:term, $p:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, $p⟩ : SimplexCategory.Truncated $n))

/-- The inclusion of `Truncated n` into `Truncated m` when `n ≤ m`. -/
abbrev incl (n m : ℕ) (h : n ≤ m := by lia) : Truncated n ⥤ Truncated m :=
  ObjectProperty.ιOfLE (fun _ h' ↦ h'.trans h)

end Truncated
end SimplexCategory
end
