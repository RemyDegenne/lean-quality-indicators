namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck8268 : row8268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8268 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
