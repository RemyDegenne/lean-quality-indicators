@[expose] public section

universe u v w u₁

namespace Set

variable {M : Type w} (A : Set M) (L : FirstOrder.Language.{u, v}) [L.Structure M]

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {α : Type u₁} {β : Type*}

variable {L} {A} {B : Set M} {s : Set (α → M)}

@[simp]
theorem Definable.union {f g : Set (α → M)} (hf : A.Definable L f) (hg : A.Definable L g) :
    A.Definable L (f ∪ g) := by
  rcases hf with ⟨φ, rfl⟩
  rcases hg with ⟨θ, rfl⟩
  refine ⟨φ ⊔ θ, ?_⟩
  ext
  simp

end Set
end
