namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck1027 : row1027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1027 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
