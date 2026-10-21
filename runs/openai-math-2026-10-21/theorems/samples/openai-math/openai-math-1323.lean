namespace OAI

noncomputable section

open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SourceConeMorphism

open KummerSourceModel

attribute [local instance] sectionParameterAlgebra completedParameterAlgebra

lemma p_eq_comparison : p = tensorEvaluation ≫ completionSpecIso.inv := rfl

end SourceConeMorphism
end
end OAI
