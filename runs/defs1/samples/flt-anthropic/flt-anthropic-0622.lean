namespace P2MW.S_Real_poitouKernel_admissible_and_archBound

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

section

namespace FLT

namespace Gapsw80T75BourbakiKernelDef

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin

open FLT.Gapsw80T13AffineArchTermA34Redecomp

open FLT.Gapsw80T18ArchDerivedA34Redecomp

open FLT.Gapsw80T21D2SubDecompWire

open FLT.Gapsw80T23OdlyzkoKernelStripRemint

open FLT.Gapsw80T69AdmC2RemintZktSummable

open FLT.Gapsw80T74B4vFloor24SubDecomp

p2m_open

def gapsw80_t75_BourbakiStripPositivity : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
    0 ≤ gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel ρ

end Gapsw80T75BourbakiKernelDef
end FLT
end
end P2MW.S_Real_poitouKernel_admissible_and_archBound
