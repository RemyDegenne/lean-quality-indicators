@[expose] public section

namespace NRR

variable {n : ℕ}

/-- Constructor for `ZeroSum n` from a function and a proof its coordinates sum to zero. -/
def ZeroSum.mk' (v : Fin n → ℝ) (hv : ∑ i, v i = 0) : ZeroSum n :=
  ⟨v, hv⟩

end NRR
end
