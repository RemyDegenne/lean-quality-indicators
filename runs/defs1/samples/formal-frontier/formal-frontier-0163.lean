set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {R : Type u} [Ring R]

variable {n : Type v} [Fintype n] [DecidableEq n]

/-- The augmentation from the general linear group of an ideal's unitization
to the general linear group over `ℤ`. -/
def idealAugmentation (I : TwoSidedIdeal R) :
    GL n (Unitization ℤ I) →* GL n ℤ :=
  mapRingHom (Unitization.fstHom (R := ℤ) (A := I)).toRingHom

end Matrix.GeneralLinearGroup
end
