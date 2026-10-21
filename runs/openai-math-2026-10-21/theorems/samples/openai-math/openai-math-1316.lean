namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck15820 : row15820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15820 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
