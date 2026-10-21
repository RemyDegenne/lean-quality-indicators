namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck11605 : row11605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11605 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
