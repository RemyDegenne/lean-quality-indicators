namespace P2MW.S_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal

attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing

open scoped AdicCompletion.GaloisAction

open scoped TensorProduct

namespace Algebra

namespace IsUnramifiedAt

namespace CH2

p2m_open

noncomputable def localizationEquiv (R : Type*) {A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B] (𝔓 : Ideal B) [𝔓.IsPrime] :
    Localization.AtPrime (𝔓.comap (algebraMap A B)) ≃ₐ[R] Localization.AtPrime 𝔓 :=
  haveI := isLocalization_atPrime_comap M 𝔓
  (IsLocalization.algEquiv (𝔓.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime (𝔓.comap (algebraMap A B))) (Localization.AtPrime 𝔓)).restrictScalars R

end CH2
end IsUnramifiedAt
end Algebra
end P2MW.S_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal
