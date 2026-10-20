namespace P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed

set_option autoImplicit false

noncomputable section

namespace CharpS10bB

namespace Model

p2m_open

variable (N : ℕ) [NeZero N]

variable (A : ValuationSubring (AlgebraicClosure ℚ))

scoped instance instIsIntegrallyClosed_BFin : IsIntegrallyClosed (BFin N A) :=
  isIntegrallyClosed_integralClosure_in_field (R' := affineBaseFin N A) (K' := FF N)

scoped instance instIsIntegrallyClosed_BInf : IsIntegrallyClosed (BInf N A) :=
  isIntegrallyClosed_integralClosure_in_field (R' := affineBaseInf N A) (K' := FF N)

def intPolyToFin : Polynomial ℤ →+* affineBaseFin N A :=
  eval₂RingHom (Int.castRingHom _) ⟨jBar N, jBar_mem_affineBaseFin N A⟩

end Model
end CharpS10bB
end
end P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed
