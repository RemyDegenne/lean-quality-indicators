namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck12672 : row12672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12672 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
