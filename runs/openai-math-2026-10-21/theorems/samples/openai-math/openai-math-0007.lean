namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck14655 : row14655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14655 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
