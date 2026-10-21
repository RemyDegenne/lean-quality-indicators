namespace OAI

namespace StableCoordinate.Presentation

open MvPolynomial MatrixChange

noncomputable section

@[simp] lemma matrixEquiv_apply (n : ℕ) (v : P n) :
    matrixEquiv n v = changeHom n (-1) v := rfl

end
end StableCoordinate.Presentation
end OAI
