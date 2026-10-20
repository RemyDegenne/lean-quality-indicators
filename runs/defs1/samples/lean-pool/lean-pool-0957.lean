@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

variable (C S A : Type*)
  [CommRing C] [CommRing S] [CommRing A]
  [Algebra C S] [Algebra C A] [Algebra C[X] A]
  [IsScalarTower C C[X] A]

local instance coefficientPolynomialAlgebra : Algebra C[X] S[X] :=
  Polynomial.algebra C S

local instance coefficientPolynomialTower : IsScalarTower C C[X] S[X] :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro c
    simp [Polynomial.algebraMap_def])

/-- Evaluate base polynomials in the constant tensor product. -/
noncomputable def constantTensorPolynomialAlgHom :
    C[X] →ₐ[C] (TensorProduct C S A) :=
  Polynomial.aeval (polynomialTensorCancelEvaluationPoint C S A)

end
end BGS.HasseWeil
end
