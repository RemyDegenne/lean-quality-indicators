namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck18876 : row18876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18876 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
