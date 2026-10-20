@[expose] public section

/-- The nth-harmonic number defined as a finset sum of consecutive reciprocals. -/
@[oeis A001008 "numerators; the sequence skips `n = 0`",
  oeis A002805 "denominators; the sequence skips `n = 0`"]
def harmonic : ℕ → ℚ := fun n => ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹

end
