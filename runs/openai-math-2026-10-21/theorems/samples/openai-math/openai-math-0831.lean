namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck18835 : row18835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18835 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
