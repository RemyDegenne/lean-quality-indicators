@[expose] public section

open Function

variable {F M N R α : Type*}

export CentroidHomClass (map_mul_left map_mul_right)

namespace CentroidHom

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

theorem toEnd_injective : Injective (CentroidHom.toEnd : CentroidHom α → AddMonoid.End α) :=
  coe_toAddMonoidHom_injective

end NonUnitalNonAssocSemiring
end CentroidHom
end
