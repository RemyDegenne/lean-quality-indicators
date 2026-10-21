namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck9927 : row9927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9927 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
