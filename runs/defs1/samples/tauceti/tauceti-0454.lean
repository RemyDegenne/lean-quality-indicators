public section

namespace TauCeti

namespace InternalHom

section Precomp

variable (G : Type*) [Group G] {M M' : Type*} [AddMonoid M] [AddMonoid M'] [DistribMulAction G M]
  [DistribMulAction G M'] {N : Type*} [AddCommMonoid N] [DistribMulAction G N]

/-- Precomposition with an equivariant homomorphism `f : M →+[G] M'`, as an equivariant homomorphism
`InternalHom G M' N →+[G] InternalHom G M N`: the internal hom is contravariantly functorial in its
source. Its values are characterized by `evalPairing_precomp`. -/
def precomp (f : M →+[G] M') : InternalHom G M' N →+[G] InternalHom G M N where
  toFun φ := of G (φ.toAddMonoidHom.comp (f : M →+ M'))
  map_smul' g φ := by
    ext m
    simp [homAction_apply, map_smul]
  map_zero' := rfl
  map_add' _ _ := rfl

end Precomp
end InternalHom
end TauCeti
end
