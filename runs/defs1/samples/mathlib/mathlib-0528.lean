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
/-- The counit of a bialgebra as a `BialgHom`. -/
noncomputable def counitBialgHom : A →ₐc[R] R :=
  { Coalgebra.counitCoalgHom R A, counitAlgHom R A with }

end Bialgebra
end
