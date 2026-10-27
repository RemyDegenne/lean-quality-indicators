@[expose] public section

open scoped Ring

namespace MulChar

attribute [scoped simp] MulCharClass.map_nonunit

section Group

variable {R : Type*} [CommMonoid R]

variable {R' : Type*} [CommMonoidWithZero R']

/-- The equivalence between multiplicative characters and homomorphisms of unit groups. -/
noncomputable def equivToUnitHom : MulChar R R' ≃ (Rˣ →* R'ˣ) where
  toFun := toUnitHom
  invFun := ofUnitHom
  left_inv := by
    intro χ
    ext x
    rw [ofUnitHom_coe, coe_toUnitHom]
  right_inv := by
    intro f
    ext x
    simp only [coe_toUnitHom, ofUnitHom_coe]

end Group
end MulChar
end
