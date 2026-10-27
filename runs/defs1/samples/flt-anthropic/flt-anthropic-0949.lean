namespace P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 80000

noncomputable section

namespace HeckeEis

namespace PairingSol

p2m_open

open MvPolynomial Finset

open scoped MatrixGroups

variable (n : ℕ)

def wt (i : ℕ) : ℂ := (-1) ^ (n - i) / (n.choose i : ℂ)

end PairingSol
end HeckeEis
end
end P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow
