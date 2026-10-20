@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

variable {R : Type u} [Ring R]

theorem constantTransformation_evaluationTransformation :
    constantTransformation ≫ evaluationTransformation = 𝟙 simplexFunctor := by
  apply NatTrans.ext
  funext A
  change constantInclusion A ≫ evalAtZero A = 𝟙 (simplex A)
  exact constantInclusion_evalAtZero A

end
end CentralPolynomialSimplex
end
