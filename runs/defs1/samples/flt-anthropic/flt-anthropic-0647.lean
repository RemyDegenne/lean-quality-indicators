namespace P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TrivSqZeroExt NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

universe u

namespace TangentDimBody

noncomputable section

section Tangent

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (k : Type u) [Field k] (sk : S →+* k)

variable (M : Type u) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]

variable {L k sk M}

variable {N : Type u} [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N] [IsCentralScalar k N]

variable {N' : Type u} [AddCommGroup N'] [Module k N'] [Module kᵐᵒᵖ N'] [IsCentralScalar k N']

p2m_reactivate

variable (f k sk) in

abbrev J : Scheme.{u} := pullback f (γ k sk)

end Tangent
end
end TangentDimBody
end P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension
