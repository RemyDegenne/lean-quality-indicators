namespace P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot

attribute [-instance] MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace L3Aux

open MvPowerSeries

section FibreProduct

variable {T k : Type*} [CommRing T] [CommRing k] (res : T →+* k)

noncomputable def π₁ : FP res →+* T := (RingHom.fst T T).comp (FP res).subtype

end FibreProduct
end L3Aux
end P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot
