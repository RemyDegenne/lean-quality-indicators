namespace P2MW.S_HeckeEis_exists_induced_binaryFormRepSL_top

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 80000

noncomputable section

namespace HeckeEis

namespace UH3Sol

p2m_open

open scoped MatrixGroups

open MvPolynomial Finset

variable (N : ℕ) (n : ℕ)

abbrev Vn := ↥(BinaryForm ℂ n)

end UH3Sol
end HeckeEis
end
end P2MW.S_HeckeEis_exists_induced_binaryFormRepSL_top
