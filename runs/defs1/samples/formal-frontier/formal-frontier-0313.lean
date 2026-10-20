@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Polynomial

open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

namespace RootsOfUnity

variable {R : Type v} [CommMonoid R]

/-- The group equivalence between roots of unity and cyclic characters. -/
def mulEquivMonoidHom (n : ℕ) :
    rootsOfUnity n R ≃* (Multiplicative (ZMod n) →* R) where
  __ := equivMonoidHom n
  map_mul' ζ ξ := by
    apply cyclicCharacter_ext
    change rootMonoidHom (ζ * ξ) (.ofAdd 1) =
      (rootMonoidHom ζ * rootMonoidHom ξ) (.ofAdd 1)
    simp only [rootMonoidHom_generator, MonoidHom.mul_apply,
      Subgroup.coe_mul, Units.val_mul]

end RootsOfUnity
end AlgebraicGeometry
end
end
