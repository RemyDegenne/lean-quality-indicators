@[expose] public section

open IsLocalRing

namespace ValuationSubring

universe u

variable {K : Type u} [Field K]

@[simp]
theorem mem_composite {A : ValuationSubring K} {W : ValuationSubring (ResidueField A)}
    {x : K} : x ∈ A.composite W ↔ ∃ hx : x ∈ A, residue A ⟨x, hx⟩ ∈ W :=
  Iff.rfl

end ValuationSubring
end
