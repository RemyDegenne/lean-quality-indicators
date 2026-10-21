namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck14066 : row14066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14066 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
