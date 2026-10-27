namespace P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped TensorProduct

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace Ws25

namespace KummerO

namespace PointsDict

open WithConv

p2m_reactivate

section Points

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {O : Type} [CommRing O] [Algebra O ↥A]
  [Algebra O (AlgebraicClosure ℚ)] [IsScalarTower O ↥A (AlgebraicClosure ℚ)]

variable (B : Type) [CommRing B] [Bialgebra O B]

noncomputable def pointsEquiv [Module.Finite O B] : WithConv (B →ₐ[O] ↥A) ≃ WithConv (B →ₐ[O] AlgebraicClosure ℚ) :=
  { toFun := toQ B
    invFun := ofQ (A := A) B
    left_inv := ofQ_toQ B
    right_inv := toQ_ofQ B }

end Points
end PointsDict
end KummerO
end Ws25
end
end P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial
