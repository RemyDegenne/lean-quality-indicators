namespace P2MW.S_AlgebraicCurve_tateAgreement_v2

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 6400000

set_option maxHeartbeats 12800000

section

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

section

section

set_option maxHeartbeats 12800000

set_option synthInstance.maxHeartbeats 6400000

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

p2m_open

p2m_open

noncomputable section

namespace ModularCurve

namespace KwF4gRRTate

p2m_open

p2m_reactivate

p2m_reactivate

section DiffTraceZero

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

variable (pA' : u.adicCompletion →ₗ[K] u.adicCompletion)

def KwF4gRRTateCommFiniteGen : Prop :=
  ∀ (h : SameRangeIdemProjectors (tateProj u) pA') (fh gh : u.adicCompletion),
    FiniteDimensional K
      (LinearMap.range (tateCommRestrict pA' (lmulK u fh) (lmulK u gh)))

end DiffTraceZero
end KwF4gRRTate
end ModularCurve
end
end
end
end
end P2MW.S_AlgebraicCurve_tateAgreement_v2
