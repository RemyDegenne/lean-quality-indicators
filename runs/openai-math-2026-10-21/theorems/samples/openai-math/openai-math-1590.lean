namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowCheck7693 : row7693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7693 := by decide +kernel

end MUB6.Certificate.GramRows
end OAI
