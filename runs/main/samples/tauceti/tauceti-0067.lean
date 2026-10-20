public section

open Finset

namespace TauCeti

variable {R E ι : Type*} [Field R] [AddCommGroup E] [Module R E] [Fintype ι]

theorem finiteMean_eq_inv_smul_sum (z : ι → E) :
    finiteMean R z = (Fintype.card ι : R)⁻¹ • ∑ i, z i := by
  simp [finiteMean_def, centerMass]

end TauCeti
end
