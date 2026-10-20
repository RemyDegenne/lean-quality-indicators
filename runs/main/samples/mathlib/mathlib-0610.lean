@[expose] public section

open CliffordAlgebra

namespace CliffordAlgebraQuaternion

open scoped Quaternion

open QuaternionAlgebra

variable {R : Type*} [CommRing R] (c₁ c₂ : R)

@[simp]
theorem Q_apply (v : R × R) : Q c₁ c₂ v = c₁ * (v.1 * v.1) + c₂ * (v.2 * v.2) :=
  rfl

end CliffordAlgebraQuaternion
end
