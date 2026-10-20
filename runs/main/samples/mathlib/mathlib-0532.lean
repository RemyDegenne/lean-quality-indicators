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

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →⋆ₙₐ[S] B) → A →⋆ₙₐ[R] B) :=
  fun _ _ h ↦ ext (DFunLike.congr_fun h :)

end RestrictScalars
end NonUnitalStarAlgHom
end
