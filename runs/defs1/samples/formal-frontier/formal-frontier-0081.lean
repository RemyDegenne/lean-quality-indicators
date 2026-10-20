set_option warningAsError true

@[expose] public section

namespace Matrix

universe uX uY uR

variable {R : Type uR} [CommRing R]

/-- Split the first index from the remaining indices, without changing their order. -/
def firstRestEquiv (n : ℕ) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n :=
  (finCongr (Nat.add_comm n 1)).trans finSumFinEquiv.symm

end Matrix
end
