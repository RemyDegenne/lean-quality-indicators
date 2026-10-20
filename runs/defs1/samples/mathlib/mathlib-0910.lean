@[expose] public section

variable {R A V : Type*}

variable [CommRing R] [CommRing A] [AddCommGroup V]

variable [Algebra R A] [Module R V]

variable [Invertible (2 : R)]

open scoped TensorProduct

namespace CliffordAlgebra

variable (A)

open MulOpposite

/-- Base-changing the vector space of a clifford algebra is isomorphic as an A-algebra to
base-changing the clifford algebra itself; $<|Cℓ(A ⊗_R V, Q_A) ≅ A ⊗_R Cℓ(V, Q)<|$.

This is `CliffordAlgebra.toBaseChange` and `CliffordAlgebra.ofBaseChange` as an equivalence. -/
@[simps!]
def equivBaseChange (Q : QuadraticForm R V) :
    CliffordAlgebra (Q.baseChange A) ≃ₐ[A] A ⊗[R] CliffordAlgebra Q :=
  AlgEquiv.ofAlgHom (toBaseChange A Q) (ofBaseChange A Q)
    (toBaseChange_comp_ofBaseChange A Q)
    (ofBaseChange_comp_toBaseChange A Q)

end CliffordAlgebra
end
