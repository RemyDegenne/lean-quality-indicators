namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck5067 : row5067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5067 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
