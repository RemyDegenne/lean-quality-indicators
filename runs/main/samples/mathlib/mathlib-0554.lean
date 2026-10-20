public section

universe u v

open Cardinal

namespace MvPolynomial

section TwoUniverses

variable {σ : Type u} {R : Type v} [CommSemiring R]

@[nontriviality]
theorem cardinalMk_eq_one [Subsingleton R] : #(MvPolynomial σ R) = 1 := mk_eq_one _

end TwoUniverses
end MvPolynomial
end
