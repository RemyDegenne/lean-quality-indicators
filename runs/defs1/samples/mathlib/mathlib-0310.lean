@[expose] public section

namespace Semiquot

variable {α : Type*} {β : Type*}

/-- Construct a `Semiquot α` from `h : a ∈ s` where `s : Set α`. -/
def mk {a : α} {s : Set α} (h : a ∈ s) : Semiquot α :=
  ⟨s, Trunc.mk ⟨a, h⟩⟩

end Semiquot
end
