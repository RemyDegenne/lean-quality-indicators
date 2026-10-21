namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck2242 : row2242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2242 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
