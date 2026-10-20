namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_etale_lev_and_forall_factorsThrough_iff_of_isUnit

set_option autoImplicit false

p2m_open

open scoped Quaternion

noncomputable section

namespace LevEtaleCritBody

section Level

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

variable (E : FakeEllipticCurve Λ N S)

def jC : E.C ⟶ E.L.schemeKer N := kerLift E.L N (tautPt E) (tautPt_torsion E)

end Level
end LevEtaleCritBody
end
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_etale_lev_and_forall_factorsThrough_iff_of_isUnit
