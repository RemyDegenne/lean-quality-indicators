@[expose] public section

universe u v w

open CategoryTheory

open scoped TensorProduct

namespace KTheory.ProjectiveClass

variable (R : Type u) [CommRing R]

/-- Tensor product of finite projective right-module classes over a commutative
ring, with tensor product taken over the opposite scalar ring. -/
@[no_expose]
noncomputable def tensorMul : ProjectiveClass R → ProjectiveClass R → ProjectiveClass R :=
  liftFunction R (tensorMulAux R) (tensorMulAux_congr R)

end KTheory.ProjectiveClass
end
