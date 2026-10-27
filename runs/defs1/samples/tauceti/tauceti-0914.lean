public section

open TauCeti.Bialgebra _root_.Bialgebra _root_.Coalgebra WithConv

namespace TauCeti

section Hopf

open TrivSqZeroExt WithConv _root_.Bialgebra Bialgebra.CounitAlgebra

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
  [CommSemiring B] [Algebra R B]

variable (R A B) in
/-- The tangent kernel at the identity is linearly equivalent to the module of derivations
at the counit point. -/
noncomputable def derivationLinearEquivTangentKer :
    Derivation R A (Bialgebra.CounitAlgebra R A B) ≃ₗ[B]
      Additive (tangentKer R A B) :=
  (((AddEquiv.additiveMultiplicative _).symm.trans
    (derivationMulEquivTangentKer R A B).toAdditive).symm.linearEquiv B).symm

end Hopf
end TauCeti
end
