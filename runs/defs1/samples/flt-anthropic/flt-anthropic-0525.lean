namespace P2MW.S_MvPolynomial_finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial

namespace TruncatedDieudonneCount

def I (p n a b : ℕ) : Ideal (MvPolynomial Bool ℤ) := Ideal.span (rels p n a b)

end TruncatedDieudonneCount
end
end P2MW.S_MvPolynomial_finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow
