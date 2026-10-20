namespace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

section

set_option maxHeartbeats 6400000

namespace FLT

namespace Gapsw80T10DedekindZetaBridgeA1Discharge

p2m_open

open FLT.Gapsw80T8MellinGammaPartialZeta FLT.Gapsw80T9ClassSumA1Closure

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition

p2m_open

p2m_open_scoped

variable (K : Type) [Field K] [NumberField K] [S18.HADPkg K]

scoped instance gapsw80_t10_fiberFinite (n : ℕ) :
    Finite {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n} := by
  haveI : Finite {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq n).to_subtype
  exact Finite.of_injective
    (fun J => (⟨J.1.1, J.2⟩ : {I : Ideal (𝓞 K) // absNorm I = n}))
    (fun J₁ J₂ h => Subtype.ext (Subtype.ext (by
      simpa only [Subtype.mk.injEq] using h)))

theorem gapsw80_t10_completedDedekindZeta_eq_T1 {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K s
      = gapsw80_t1_completedDedekindZeta K s :=
  S18.HADPkg.eqT1 s hs

end Gapsw80T10DedekindZetaBridgeA1Discharge
end FLT
end
end P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package
