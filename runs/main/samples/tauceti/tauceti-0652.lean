public section

open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

theorem rep_serreRootGenerator_inr_latticeBasis_eq_sum (i : Fin 4) (s : Fin 24) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator weightTable.cartanMatrix (.inr i)))
        ((latticeBasis s : lattice) : Fin 24 → ℚ) =
      ∑ r, loweringMatrix i r s • ((latticeBasis r : lattice) : Fin 24 → ℚ) := by
  rw [rep_def, loweringMatrix_def]
  simpa only [coe_latticeBasis, TauCeti.coe_coordinateLatticeBasis, Pi.basisFun_apply] using
    weightTable.rep_serreRootGenerator_inr_coordinateLatticeBasis_eq_sum i s

end TauCeti.D4Tripled
end
