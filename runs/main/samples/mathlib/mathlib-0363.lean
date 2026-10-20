@[expose] public section

namespace Rat

protected lemma inv_nonneg {a : ℚ} (ha : 0 ≤ a) : 0 ≤ a⁻¹ := by
  rw [inv_def]
  exact divInt_nonneg (Int.natCast_nonneg a.den) (num_nonneg.mpr ha)

end Rat
end
