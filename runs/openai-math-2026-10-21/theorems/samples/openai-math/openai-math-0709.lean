namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck15579 : row15579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15579 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
