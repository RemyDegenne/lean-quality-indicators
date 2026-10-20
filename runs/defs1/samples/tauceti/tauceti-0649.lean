public section

open Module

namespace TauCeti

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntegralLattice

open Classical in
/-- The basis of the dual carrier corresponding to a `ℤ`-basis of `L.carrier`. -/
noncomputable def dualCarrierBasis (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type*} [Finite ι] (b : Basis ι ℤ L.carrier) :
    Basis ι ℤ L.dualCarrier :=
  b.dualBasis.map L.dualPairingEquiv.symm

end IntegralLattice
end TauCeti
end
