set_option warningAsError true

@[expose] public section

namespace Matrix

universe u

variable {I : Type u} [NonUnitalRing I]

variable {n : ℕ}

namespace GeneralLinearGroup

universe v

variable {n : Type v} [Fintype n] [DecidableEq n]

/-- The general linear group of an arbitrary nonunital ring, defined as the
kernel of the augmentation on its canonical unitization. -/
def nonUnitalGeneralLinearGroup : Subgroup (GL n (Unitization ℤ I)) :=
  MonoidHom.ker (nonUnitalAugmentation (n := n) (I := I))

end GeneralLinearGroup
end Matrix
end
