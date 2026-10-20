@[expose] public section

open IsLocalization Pointwise nonZeroDivisors

namespace FractionalIdeal

open Set Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]

variable [Algebra R P]

variable (S)

variable {S}

variable (S)

variable {S}

variable (S P)

/-- `FractionalIdeal.coeToSubmodule` as a bundled `RingHom`. -/
@[simps]
def coeSubmoduleHom : FractionalIdeal S P →+* Submodule R P where
  toFun := coeToSubmodule
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero (S := S)
  map_add' := coe_add

end FractionalIdeal
end
