namespace P2MW.S_NumberField_archTermDerived_le_log_abs_discr

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

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

namespace FLT

namespace Gapsw80T69AdmC2RemintZktSummable

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin

open FLT.Gapsw52T2CarrierContentAtoms

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition

open FLT.Gapsw80T9ClassSumA1Closure

open FLT.Gapsw80T13AffineArchTermA34Redecomp

open FLT.Gapsw80T18ArchDerivedA34Redecomp

open FLT.Gapsw80T19B2ppHadamardDecomp

open FLT.Gapsw80T21D2SubDecompWire

open FLT.Gapsw80T23OdlyzkoKernelStripRemint

open FLT.Gapsw80T24StripMigrationChainStart

open FLT.Gapsw80T25B4pppStripSinglePointAbsorption

open FLT.Gapsw80T62ArchGammaKernelRemintWire

open FLT.Gapsw80T64D2fGaussianMollificationProof

open FLT.Gapsw80T67D2bpPrimeSumFalseprobeRemint

open FLT.Gapsw80T68D2bppExplicitFormulaSubDecomp

p2m_open

def gapsw80_t69_KernelC2Decay (F : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 F ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|))

end Gapsw80T69AdmC2RemintZktSummable
end FLT
end
end P2MW.S_NumberField_archTermDerived_le_log_abs_discr
