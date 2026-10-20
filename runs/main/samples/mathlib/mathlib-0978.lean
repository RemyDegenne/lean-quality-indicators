@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace IdealSheafData

variable (I : IdealSheafData X)

section Semiring

variable (I J K : X.IdealSheafData)

@[simp] lemma mul_top : I * ⊤ = I := by ext; simp

end Semiring
end IdealSheafData
end AlgebraicGeometry.Scheme
end
