namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck18509 : row18509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18509 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
