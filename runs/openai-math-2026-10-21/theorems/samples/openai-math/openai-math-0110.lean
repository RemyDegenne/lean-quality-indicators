namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck15072 : row15072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15072 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
