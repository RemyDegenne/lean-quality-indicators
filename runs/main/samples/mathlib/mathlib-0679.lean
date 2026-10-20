@[expose] public section

noncomputable section

open Finsupp Finset Function

namespace MvPowerSeries

section CommSemiring

variable {σ R : Type*} [CommSemiring R]

section finSuccEquiv

variable {n : ℕ}

theorem finSuccEquiv_comp_C : (MvPowerSeries.finSuccEquiv R n).symm.toRingHom.comp
    (PowerSeries.C.comp MvPowerSeries.C) = MvPowerSeries.C := by
  ext1; simp [AlgEquiv.symm_apply_eq]

end finSuccEquiv
end CommSemiring
end MvPowerSeries
end
end
