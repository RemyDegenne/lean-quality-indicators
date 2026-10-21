namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck9342 : row9342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9342 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
