namespace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

namespace FLT

namespace Gapsw80T20LambdaLogDerivProductRule

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition

open FLT.Gapsw80T9ClassSumA1Closure

open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge

open FLT.Gapsw80T19B2ppHadamardDecomp

p2m_open

variable (K : Type) [Field K] [NumberField K] [S18.HADPkg K]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t20_eventuallyEq_T1 {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t9_completedDedekindZeta K) =ᶠ[nhds s]
      (gapsw80_t1_completedDedekindZeta K) := by
  have _em := Classical.em
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨{z : ℂ | 1 < z.re}, hopen.mem_nhds hs,
      fun z hz => gapsw80_t10_completedDedekindZeta_eq_T1 K hz⟩

end Gapsw80T20LambdaLogDerivProductRule
end FLT
end
end P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package
