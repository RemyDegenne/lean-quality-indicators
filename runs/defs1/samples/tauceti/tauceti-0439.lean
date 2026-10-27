public section

namespace TauCeti

namespace BasedUnorientedGaussCode

variable {n : ℕ}

/-- Mirror a based unoriented Gauss code. -/
def mirror (D : BasedUnorientedGaussCode n) : BasedUnorientedGaussCode n :=
  Quotient.map' BasedOrientedGaussCode.mirror (by
    intro E F h
    apply (BasedOrientedGaussCode.unorientedSetoid_apply _ _).mpr
    rcases (BasedOrientedGaussCode.unorientedSetoid_apply E F).mp h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h ▸ BasedOrientedGaussCode.mirror_reverse F)) D

end BasedUnorientedGaussCode
end TauCeti
end
