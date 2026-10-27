@[expose] public section

open TensorProduct Bialgebra Coalgebra Function

universe u v w

@[inherit_doc BialgHom]
infixr:25 " →ₐc " => BialgHom _

@[inherit_doc]
notation:25 A " →ₐc[" R "] " B => BialgHom R A B

namespace Bialgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

variable (R A) in
/-- The unit of a bialgebra as a `BialgHom`. -/
noncomputable def unitBialgHom : R →ₐc[R] A :=
  .ofAlgHom (Algebra.ofId R A) (by ext) (by ext)

end Bialgebra
end
