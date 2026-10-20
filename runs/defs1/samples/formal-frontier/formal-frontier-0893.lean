public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- The additive group scheme over `K`. -/
abbrev additiveGroupScheme
    (K : Type u) [CommRing K] : Grp (Over (Spec (.of K))) :=
  ⟨additiveGroupUnderlyingScheme K⟩

end AlgebraicGeometry
end
end
