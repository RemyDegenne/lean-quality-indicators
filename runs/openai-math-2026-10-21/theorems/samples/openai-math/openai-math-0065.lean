namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck7448 : row7448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7448 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
