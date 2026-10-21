namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck8872 : row8872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8872 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
