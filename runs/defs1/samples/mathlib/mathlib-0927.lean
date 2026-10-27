@[expose] public section

universe u v w z

open Function

variable {α α₁ α₂ β β₁ β₂ γ : Sort*}

namespace Equiv

section

open Subtype

section

attribute [local simp] Trans.trans sigmaAssoc subtypeEquiv subtypeSigmaEquiv uniqueSigma
  eqRec_eq_cast

/-- A specialization of `sigmaSigmaSubtype` to the case where the second base
does not depend on the first, and the property being checked for is simple
equality. Useful e.g. when `γ` is `Hom` inside a category. -/
def sigmaSigmaSubtypeEq {α β : Type*} {γ : α → β → Type*} (a : α) (b : β) :
    {s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b} ≃ γ a b :=
  have : Unique (@Subtype ((_ : α) × β) (fun ⟨a', b'⟩ ↦ a' = a ∧ b' = b)) := {
    default := ⟨⟨a, b⟩, ⟨rfl, rfl⟩⟩
    uniq := by rintro ⟨⟨a', b'⟩, ⟨rfl, rfl⟩⟩; rfl }
  sigmaSigmaSubtype (fun ⟨a', b'⟩ ↦ a' = a ∧ b' = b) ⟨rfl, rfl⟩

end
end
end Equiv
end
