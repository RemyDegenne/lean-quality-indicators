namespace P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO

set_option autoImplicit false

p2m_open

open scoped ENNReal NNReal

namespace FrobeniusDensity

p2m_open

variable {K : Type*} [Field K] [NumberField K]

section normRpow

variable {s : ℝ}

lemma normRpow_ne_top {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hs : 0 ≤ s) : normRpow K s I ≠ ∞ :=
  ((normRpow_le_one hI hs).trans_lt ENNReal.one_lt_top).ne

end normRpow
end FrobeniusDensity
end P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO
