public section

namespace TauCeti

variable (G M A : Type*) [Monoid G] [Monoid M] [CommGroup A]
  [MulDistribMulAction G M] [MulDistribMulAction G A]

/-- Equivariant characters as subgroup elements or bundled equivariant homomorphisms. -/
def equivariantCharacterEquiv : equivariantCharacterSubgroup G M A ≃ (M →*[G] A) where
  toFun χ := { χ.val with map_smul' := χ.property }
  invFun χ := ⟨χ.toMonoidHom, χ.map_smul⟩
  left_inv _ := rfl
  right_inv _ := rfl

end TauCeti
end
