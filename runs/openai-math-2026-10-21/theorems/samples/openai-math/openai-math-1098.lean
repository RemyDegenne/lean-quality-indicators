namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck15770 : row15770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15770 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
