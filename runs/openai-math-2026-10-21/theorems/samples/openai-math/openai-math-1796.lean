namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck14340 : row14340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14340 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
