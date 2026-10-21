namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck15109 : row15109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15109 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
