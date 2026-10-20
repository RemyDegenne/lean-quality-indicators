@[expose] public section

open Function

variable {F M N R α : Type*}

export CentroidHomClass (map_mul_left map_mul_right)

namespace CentroidHom

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

variable (α)

variable {α}

variable [Monoid M] [Monoid N] [Semiring R]

variable [DistribMulAction M α] [SMulCommClass M α α] [IsScalarTower M α α]

variable [DistribMulAction N α] [SMulCommClass N α α] [IsScalarTower N α α]

variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]

variable {R : Type*}

variable [CommSemiring R]

variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]

local notation "L" => AddMonoid.End.mulLeft

local notation "R" => AddMonoid.End.mulRight

/-- The canonical homomorphism from the center into the centroid -/
def centerToCentroid : NonUnitalSubsemiring.center α →ₙ+* CentroidHom α :=
  NonUnitalRingHom.comp
    (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
    centerToCentroidCenter

end NonUnitalNonAssocSemiring
end CentroidHom
end
