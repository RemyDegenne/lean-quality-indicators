public noncomputable section

open Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups

namespace TauCeti

variable (N : ℕ) [NeZero N] (k : ℤ)

theorem heckeTCuspPrimeAlgebra_le_heckeTCuspAlgebra :
    heckeTCuspPrimeAlgebra N k ≤ heckeTCuspAlgebra N k :=
  (heckeTCuspPrimeAlgebra_le_iff N k _).mpr fun p hp ↦
    @heckeTCuspNat_mem_heckeTCuspAlgebra N _ k p ⟨hp.ne_zero⟩

end TauCeti
end
