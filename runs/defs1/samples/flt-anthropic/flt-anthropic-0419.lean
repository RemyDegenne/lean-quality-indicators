namespace P2MW.S_HopfAlgebra_isHopfGalois_of_surjective

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped TensorProduct

open HopfAlgebra Coalgebra

universe u v w

namespace S17KT

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]

variable {B : Type w} [CommRing B] [HopfAlgebra R B]

variable (π : A →ₐc[R] B)

noncomputable def T (φ : Module.Dual R B) : A →ₗ[R] A := G φ ∘ₗ (coaction π).toLinearMap

end S17KT
end P2MW.S_HopfAlgebra_isHopfGalois_of_surjective
