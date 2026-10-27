namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_sqZero_of_natCast_eq_zero

set_option autoImplicit false

set_option maxHeartbeats 3200000

p2m_open

open scoped TensorProduct

universe u

noncomputable section

namespace GoodReductionJacobian

p2m_open

namespace RelativeGroupLaw

p2m_open

variable {R : Type u} [CommRing R]

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

open CategoryTheory.Limits

abbrev kwPairingMap : Limits.pullback f f ⟶ Spec (CommRingCat.of R) :=
  Limits.pullback.fst f f ≫ f

end RelativeGroupLaw
end GoodReductionJacobian
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_sqZero_of_natCast_eq_zero
