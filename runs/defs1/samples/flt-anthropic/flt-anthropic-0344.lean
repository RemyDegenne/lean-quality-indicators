namespace P2MW.S_AlgebraicCurve_tateAgreement

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

p2m_reactivate

section CohenMint

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

variable [HasCanonicalLocalResidueKStar K L]

def KwF4gRRTateCohenTateAgreement : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue],
    ∃ (pC : u.adicCompletion →ₗ[K] u.adicCompletion)
      (hpC : SameRangeIdemProjectors (tateProj u) pC),
    ∀ (fh : u.adicCompletion)
      [FiniteDimensional K (LinearMap.range
        (tateCommRestrict pC (lmulK u fh)
          (lmulK u (algebraMap L u.adicCompletion u.uniformizer))))],
    tateCommTrace pC (lmulK u fh) (lmulK u (algebraMap L u.adicCompletion u.uniformizer))
      = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh)

end CohenMint
end KwF4gRRTate
end ModularCurve
end
end
end
end
end P2MW.S_AlgebraicCurve_tateAgreement
