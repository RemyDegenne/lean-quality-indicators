public section

open CategoryTheory WithConv

open TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra

open scoped TensorProduct

namespace TauCeti.D4Tripled

universe v

attribute [local instance] TauCeti.moduleNNRat

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

variable (A : Type v) [CommRing A]

theorem coordinateMap_X_eq_zero {a b : Fin 24} (hab : d4TripledSummand a ≠ d4TripledSummand b) :
    (coordinateMap A).hom (GeneralLinear.coordinateHopfAlgebraAlgEquiv A 24
      (GeneralLinear.coordinateRingMap A 24 (MvPolynomial.X (a, b)))) = 0 := by
  have hmem : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ 24
      (GeneralLinear.coordinateRingMap ℤ 24 (MvPolynomial.X (a, b))) ∈ definingIdeal := by
    apply weightLeviDefiningHopfIdeal_le_definingIdeal
    rw [← HopfIdeal.mem_toIdeal, ← Ideal.Quotient.eq_zero_iff_mem]
    exact GeneralLinear.weightLeviQuotient_mk_genericMatrix_apply_of_ne ℤ d4TripledSummand hab
  have h := map_tmul_mem_baseChangeDefiningIdeal_of_mem A 1 hmem
  rw [GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply, MvPolynomial.map_X,
    one_smul] at h
  rw [← RingHom.mem_ker, coordinateMap_ker]
  exact h

end TauCeti.D4Tripled
end
