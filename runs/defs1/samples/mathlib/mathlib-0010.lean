@[expose] public section

open EquivLike

@[inherit_doc NonUnitalStarAlgHom] infixr:25 " →⋆ₙₐ " => NonUnitalStarAlgHom _

@[inherit_doc] notation:25 A " →⋆ₙₐ[" R "] " B => NonUnitalStarAlgHom R A B

namespace NonUnitalStarAlgHom

section RestrictScalars

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S] [Star A] [Star B]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

/-- If a monoid `R` acts on another monoid `S`, then a non-unital star algebra homomorphism
over `S` can be viewed as a non-unital star algebra homomorphism over `R`. -/
def restrictScalars (f : A →⋆ₙₐ[S] B) : A →⋆ₙₐ[R] B :=
  { (f : A →ₙₐ[S] B).restrictScalars R with
    map_star' := map_star f }

end RestrictScalars
end NonUnitalStarAlgHom
end
