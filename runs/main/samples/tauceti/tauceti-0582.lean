public section

open CategoryTheory TensorProduct WithConv

open scoped commutatorElement

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule

universe v w

variable {L : Type v} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra.IsKilling ℚ L]
  [FiniteDimensional ℚ L] {H : LieSubalgebra ℚ L} [H.IsCartanSubalgebra]
  [LieModule.IsTriangularizable ℚ H L]

attribute [local instance high] Algebra.toModule

namespace IsSl2System

variable {x : Weight ℚ H L → L} (hx : IsSl2System x)

include hx

theorem isNilpotent_representation_rootVector (α : Weight ℚ H L) :
    IsNilpotent (UniversalEnvelopingAlgebra.representation ℚ L L
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (x α))) := by
  rw [UniversalEnvelopingAlgebra.representation_ι_ad]
  exact hx.isNilpotent_ad_rootVector α

end IsSl2System
end TauCeti
end
