namespace P2MW.S_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq

set_option autoImplicit false

set_option maxSynthPendingDepth 3

open IsDedekindDomain

open scoped nonZeroDivisors

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 80000

set_option Elab.async false

namespace P2mS25F0c

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

open scoped nonZeroDivisors

noncomputable section

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]

section counts

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

def content (x : (FiniteAdeleRing R F)ˣ) : FractionalIdeal R⁰ F :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ F) ^ expAt R F x v

end counts
end
end P2mS25F0c
end P2MW.S_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq
