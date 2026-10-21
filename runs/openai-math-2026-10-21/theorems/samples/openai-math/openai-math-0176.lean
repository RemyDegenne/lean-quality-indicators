namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck2981 : row2981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2981 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
