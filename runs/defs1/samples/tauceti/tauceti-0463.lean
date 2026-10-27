public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.SpecialLinear

universe u

variable {R : Type u} [CommRing R] {N : ℕ} {i j : Fin N}

/-- The closed special-linear root subgroup is canonically isomorphic to `𝔾ₐ`. -/
noncomputable def rootSubgroupClosedSubgroupIso (hij : i ≠ j) :
    ((rootSubgroupClosedSubgroup (R := R) hij).1 :
      Grp (Over (Spec (CommRingCat.of R)))) ≅ AdditiveGroup.groupScheme R :=
  ClosedSubgroupScheme.mkIso (rootSubgroup hij)

end TauCeti.SpecialLinear
end
