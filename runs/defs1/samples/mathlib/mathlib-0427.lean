@[expose] public section

open Multiset

variable {α β γ : Type*}

namespace Finset

section Diag

variable (s t : Finset α)

/-- Given a finite set `s`, the off-diagonal, `s.offDiag` is the set of pairs `(a, b)` with `a ≠ b`
for `a, b ∈ s`. -/
def offDiag : Finset (α × α) :=
  .mk (Quotient.map List.offDiag (fun _ _ ↦ List.Perm.offDiag) s.1) <| by
    rcases s with ⟨⟨s⟩, hs⟩
    exact hs.offDiag

end Diag
end Finset
end
