@[expose] public section

universe t t' w w' u v

open TensorProduct Module MvPolynomial

namespace Algebra

variable (R : Type u) (S : Type v) (ι : Type w) (σ : Type t) [CommRing R] [CommRing S] [Algebra R S]

variable [Finite σ]

namespace SubmersivePresentation

open PreSubmersivePresentation

section Constructions

section BaseChange

variable (T) [CommRing T] [Algebra R T] (P : SubmersivePresentation R S ι σ)

variable {R S ι σ} in
/-- If `P` is a submersive presentation of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural submersive presentation of `T ⊗[R] S` over `T`. -/
noncomputable def baseChange : SubmersivePresentation T (T ⊗[R] S) ι σ where
  toPreSubmersivePresentation := P.toPreSubmersivePresentation.baseChange T
  jacobian_isUnit :=
    P.baseChange_jacobian T ▸ P.jacobian_isUnit.map TensorProduct.includeRight

end BaseChange
end Constructions
end SubmersivePresentation
end Algebra
end
