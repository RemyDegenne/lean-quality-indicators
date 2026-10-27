public section

open Function Set

open CategoryTheory

universe u v w

namespace ModuleCat

variable (R : Type u) [CommRing R]

namespace ComponentwiseFreeFiniteProjective

variable {R}

/-- A linear equivalence between the underlying modules lifts to an
isomorphism in the componentwise-free full subcategory. -/
noncomputable def isoOfLinearEquiv
    {X Y : ComponentwiseFreeFiniteProjective R} (e : X.obj ≃ₗ[R] Y.obj) :
    X ≅ Y :=
  InducedCategory.isoMk (InducedCategory.isoMk e.toModuleIso)

end ComponentwiseFreeFiniteProjective
end ModuleCat
end
