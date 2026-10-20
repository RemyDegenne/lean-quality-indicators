public section

namespace TauCeti

open _root_.Coalgebra TensorProduct

namespace Bialgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The augmentation ideal of a commutative bialgebra, the kernel of its counit. -/
abbrev AugmentationIdeal :=
  RingHom.ker (_root_.Bialgebra.counitAlgHom R A : A →+* R)

end Bialgebra
end TauCeti
end
