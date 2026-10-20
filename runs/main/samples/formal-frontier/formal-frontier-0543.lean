@[expose] public section

universe u v

namespace ToricIdeals.RationalNormalCurve

variable (R : Type u) [CommRing R]

section

variable (n : ℕ)

theorem axisProjection_comp_axisSection :
    (axisProjection R n).comp (axisSection R n) = AlgHom.id R (Polynomial R) := by
  exact AlgHom.ext (axisProjection_axisSection R n)

end
end ToricIdeals.RationalNormalCurve
end
