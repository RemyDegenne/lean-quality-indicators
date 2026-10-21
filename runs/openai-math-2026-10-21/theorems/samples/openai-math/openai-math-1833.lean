namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck16130 : row16130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16130 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
