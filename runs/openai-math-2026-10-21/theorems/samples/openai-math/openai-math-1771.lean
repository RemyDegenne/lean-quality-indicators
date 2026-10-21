namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck13425 : row13425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13425 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
