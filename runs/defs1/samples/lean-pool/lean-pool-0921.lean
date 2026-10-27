@[expose] public section

open Lean LentilLib

namespace TLA

/-- Existential quantification over temporal predicates. -/
def tlaExists {α : Sort u} {β : Type v} (p : α → pred β) : pred β := fun σ => ∃ x, p x σ

end TLA
end
