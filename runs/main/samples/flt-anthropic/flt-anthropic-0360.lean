namespace P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi

set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField

namespace BZeroSol

variable (K : Type*) [Field K] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

variable (hdeg : Module.finrank (Kj K) (Top K ℓ) = dedekindPsi ℓ)

include hdeg in
theorem natDegree_minpoly : (minpoly (Kj K) (jqNModC K ℓ)).natDegree = ℓ + 1 := by
  rw [← adjoin.finrank (isIntegral_jl K ℓ hdeg), finrank_Top K ℓ hdeg]

end BZeroSol
end
end P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi
