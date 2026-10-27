namespace P2MW.S_groupCohomology_exists_injective_dual_continuousH2_archimedean

set_option autoImplicit false

p2m_open

namespace ArchInvProof

variable (p : ℕ) [Fact p.Prime]

noncomputable abbrev Mc : Rep (ZMod p) Gc := ofChar (k := ZMod p) ((cycloChar p).comp archimedeanLoc)

end ArchInvProof
end P2MW.S_groupCohomology_exists_injective_dual_continuousH2_archimedean
