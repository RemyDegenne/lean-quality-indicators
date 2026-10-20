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

scoped instance stalkAlgebra : Algebra k ((J f k sk).presheaf.stalk (jpt L k sk)) :=
  (((J f k sk).presheaf.germ ⊤ (jpt L k sk) trivial).hom.comp
    ((fJ f k sk).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra

p2m_reactivate

scoped instance isLocalHom_liftHom (g : ωJ L k sk →ₗ[k] M) :
    IsLocalHom (CommRingCat.ofHom (liftHom g).toRingHom).hom :=
  isLocalHom_of_fst_eq (liftHom g).toRingHom (fst_liftHom g)

scoped instance isLocalHom_fstHom' : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k M).toRingHom).hom :=
  isLocalHom_fstHom

p2m_reactivate

def toTJ (P : SchemeHomOver (tangentBase k sk) f) (hP : IsTangentVector L k sk P) : TJ L k sk k :=
  ⟨castBase tangentBase_eq P, toTJ_prop P hP⟩

end Tangent
end
end TangentDimBody
end P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension
