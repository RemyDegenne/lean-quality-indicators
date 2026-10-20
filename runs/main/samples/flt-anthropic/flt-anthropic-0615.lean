namespace P2MW.S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd

set_option synthInstance.maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

attribute [-instance] Quotient.instLE_mathlib

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_SIdeleSplit

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

noncomputable section

namespace M4aHerbrand

namespace SIdeleSplit

p2m_open

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum M4aLocalCFT M4aLocalCFT.HerbrandPair

p2m_open

open M4aHerbrand.SIdele M4aHerbrand.SIdeleFiniteness M4aHerbrand.FinSIdele M4aHerbrand.HerbrandPi

open scoped TensorProduct

attribute [local instance] M4aHerbrand.Bridge.moduleFinite_ringOfIntegers

section Parts

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]

theorem joinIdele_infProj_finProj (u : (AdeleRing (𝓞 L) L)ˣ) : joinIdele L (infProj L u) (finProj L u) = u :=
  Units.ext rfl

end Parts
end SIdeleSplit
end M4aHerbrand
end
end Fold_SIdeleSplit
end P2MW.S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
