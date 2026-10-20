set_option autoImplicit false

set_option warningAsError true

public section

open CategoryTheory

noncomputable section

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

namespace CorestrictionTransversal

variable (X : TopRep.{max v w} k G)

attribute [local instance] jointlyContinuous_mackeyStabilizer

variable (X : TopRep.{max v w} k G)

/-- The finite native degree-one Mackey sum over `H \\ G / K`. -/
noncomputable def mackeyDoubleCosetOneSum
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G] :
    continuousCohomology 1 (TopRep.res H.subtype X) ⟶
      continuousCohomology 1 (TopRep.res K.subtype X) := by
  let _ : LocallyCompactSpace H := H.isOpen'.locallyCompactSpace
  let _ : LocallyCompactSpace K := K.isOpen'.locallyCompactSpace
  exact (degreeOneIso (TopRep.res H.subtype X)).inv ≫
    TopModuleCat.ofHom (mackeyDoubleCosetSum X H K) ≫
      (degreeOneIso (TopRep.res K.subtype X)).hom

end CorestrictionTransversal
end ContinuousCohomology
end
end
