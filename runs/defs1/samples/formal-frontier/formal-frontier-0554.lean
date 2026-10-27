@[expose] public section

universe uR uM uN

open scoped TensorProduct

namespace KTheory.K0

variable (R : Type uR) [CommRing R]

/-- The ring homomorphism from the tensor semiring of finite projective
right-module classes to K₀. Its additive map is the completion map. -/
noncomputable def ofClassRingHom : ProjectiveClass R →+* K0 R :=
  Algebra.GrothendieckAddGroup.ofRingHom (ProjectiveClass R)

end KTheory.K0
end
