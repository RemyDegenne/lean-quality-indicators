set_option autoImplicit false

set_option warningAsError true

public section

open CategoryTheory

noncomputable section

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.jointlyContinuous_res_trans

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

namespace CorestrictionTransversal

/-- Degree-one transport from a flattened subgroup to the corresponding
nested subgroup, expressed through crossed homomorphisms. -/
noncomputable def transDegreeOne (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace (OpenSubgroup.trans H K)]
    [LocallyCompactSpace K] :
    continuousCohomology 1
        (TopRep.res (OpenSubgroup.trans H K).subtype X) ⟶
      continuousCohomology 1
        (TopRep.res K.subtype (TopRep.res H.subtype X)) :=
  (degreeOneIso
      (TopRep.res (OpenSubgroup.trans H K).subtype X)).inv ≫
    TopModuleCat.ofHom (crossedQuotientTrans X H K) ≫
      (degreeOneIso
        (TopRep.res K.subtype (TopRep.res H.subtype X))).hom

end CorestrictionTransversal
end ContinuousCohomology
end
end
