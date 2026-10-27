@[expose] public section

namespace Sabidussi

open scoped BigOperators

/-- Bracketing with a fixed left argument, as an additive homomorphism. -/
def bracketRightHom (x : Color) : Color →+ F₂ where
  toFun := bracket x
  map_zero' := bracket_zero_right x
  map_add' := bracket_add_right x

end Sabidussi
end
