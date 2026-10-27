@[expose] public section

open EquivLike

@[inherit_doc NonUnitalStarAlgHom] infixr:25 " →⋆ₙₐ " => NonUnitalStarAlgHom _

@[inherit_doc] notation:25 A " →⋆ₙₐ[" R "] " B => NonUnitalStarAlgHom R A B

@[inherit_doc StarAlgHom] infixr:25 " →⋆ₐ " => StarAlgHom _

@[inherit_doc] notation:25 A " →⋆ₐ[" R "] " B => StarAlgHom R A B

namespace NonUnitalStarAlgHom

section InlInr

variable (R A B : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
  [StarAddMonoid A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]

/-- The left injection into a product is a non-unital algebra homomorphism. -/
def inl : A →⋆ₙₐ[R] A × B :=
  prod 1 0

end InlInr
end NonUnitalStarAlgHom
end
