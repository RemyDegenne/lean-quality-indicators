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

set_option maxHeartbeats 800000 in
-- Normalizing the nested degree-one map expands the quotient comparisons.
lemma transDegreeOne_eq_map (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X]
    [LocallyCompactSpace (OpenSubgroup.trans H K)] [LocallyCompactSpace K] :
    transDegreeOne X H K =
      map (transContinuousHom H K) (transCoeffHom X H K) 1 := by
  simp only [transDegreeOne]
  rw [degreeOneIso_trans]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end CorestrictionTransversal
end ContinuousCohomology
end
end
