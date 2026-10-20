namespace P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing

open IsLocalRing RingTheory

namespace Ws14Port

universe u v

open IsLocalRing RingTheory RingTheory.Sequence Module

p2m_reactivate

p2m_reactivate

section

p2m_open

noncomputable section

namespace Module

open Module

variable {R : Type*} [CommRing R] [IsLocalRing R]

section Transport

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

def quotSMulTopQuotSMulTopComm (M : Type*) [AddCommGroup M] [Module R M] (x z : R) :
    QuotSMulTop x (QuotSMulTop z M) ≃ₗ[R] QuotSMulTop z (QuotSMulTop x M) :=
  (quotSMulTopQuotSMulTopEquivSup M z x).trans <|
    (Submodule.quotEquivOfEq _ _ (sup_comm _ _)).trans
      (quotSMulTopQuotSMulTopEquivSup M x z).symm

end Transport
end Module
end
end
end Ws14Port
end P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing
