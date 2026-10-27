@[expose] public section

noncomputable section

universe u

namespace Matrix

variable (ι : Type u) [Fintype ι] [DecidableEq ι] (R : Type u) [CommRing R]

namespace DiagonalGroup

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Entrywise coefficient change of native diagonal matrix units. -/
def map (f : R →+* S) : DiagonalGroup ι R →* DiagonalGroup ι S where
  toFun g := ⟨GeneralLinearGroup.map f g.1, by
    intro i j hij
    rw [GeneralLinearGroup.map_apply, g.2 i j hij, map_zero]⟩
  map_one' := by
    apply Subtype.ext
    exact (GeneralLinearGroup.map f).map_one
  map_mul' g h := by
    apply Subtype.ext
    exact (GeneralLinearGroup.map f).map_mul g.1 h.1

end DiagonalGroup
end Matrix
end
end
