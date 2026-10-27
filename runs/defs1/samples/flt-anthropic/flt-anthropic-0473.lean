namespace P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff

set_option autoImplicit false

p2m_open

open scoped nonZeroDivisors

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 80000

set_option Elab.async false

p2m_open

namespace IsDedekindDomain

namespace FiniteAdeleRing

namespace Ws25E5

p2m_open

noncomputable section

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

def assocIdeal (x : (FiniteAdeleRing R K)ˣ) : FractionalIdeal R⁰ K :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (expAt R K v x)

end
end Ws25E5
end FiniteAdeleRing
end IsDedekindDomain
end P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff
