namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck13786 : row13786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13786 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
