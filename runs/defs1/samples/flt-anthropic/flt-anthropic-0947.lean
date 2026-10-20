namespace P2MW.S_ModularCurve_full_eq_adjoin_primes

set_option autoImplicit false

noncomputable section

p2m_open

namespace ModularCurve

namespace W1

p2m_open

variable {K : Type*} [Field K] [Algebra ℚ K]

def cycUnit (N : ℕ) [NeZero N] : (CyclotomicField N ℚ)ˣ :=
  ((exists_isPrimitiveRoot_cyclotomicField N).choose_spec.isUnit (NeZero.ne N)).unit

end W1
end ModularCurve
end
end P2MW.S_ModularCurve_full_eq_adjoin_primes
