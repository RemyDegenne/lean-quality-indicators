@[expose] public section

open Function Monoid.Coprod

noncomputable section

namespace MarshallHall

namespace GeneralGrushko

universe u

variable {G H : Type u} [Group G] [Group H]

/-- A tuple is minimal when its total canonical syllable length is least in its
Nielsen-equivalence class. -/
def NielsenMinimal {n : ℕ} (x : Fin n → G ∗ H) : Prop :=
  ∀ y, NielsenEquivalent x y → tupleFactorLength x ≤ tupleFactorLength y

end GeneralGrushko
end MarshallHall
end
end
