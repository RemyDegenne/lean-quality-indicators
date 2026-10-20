public section

open scoped Quaternion TensorProduct

namespace TauCeti

namespace QuaternionAlgebra

open _root_.QuaternionAlgebra (Basis)

section CommRing

variable {R : Type*} [CommRing R] (a b c : R)

@[simp] theorem squareBasis_i :
    (squareBasis a b c).i = (Basis.self R).i ⊗ₜ (Basis.self R).i := (rfl)

end CommRing
end QuaternionAlgebra
end TauCeti
end
