namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck17065 : row17065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17065 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
