@[expose] public section

namespace BGS.Markoff

open Polynomial

variable {K : Type*} [Field K]

theorem splitTraceCoverPolynomial_normalized_not_irreducible_when_exponents_equal_char
    [PerfectField K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (sigma : K) :
    ¬ Irreducible (splitTraceCoverPolynomial (1 : K) sigma p p) := by
  simpa using
    (splitTraceCoverPolynomial_normalized_not_irreducible_when_char_mul_exponents
      (K := K) p sigma 1 1)

end BGS.Markoff
end
