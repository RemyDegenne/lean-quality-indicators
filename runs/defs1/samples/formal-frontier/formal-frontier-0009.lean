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

/-- Decomposition of the ambient group through two nested right transversals.
The inverse computes when constructing the composite right transversal. -/
@[expose]
noncomputable def towerDecompositionEquiv (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal) :
    G ≃ K × (↥(U : Set H) × ↥(T : Set G)) :=
  T.2.equiv |>.trans <|
    (Equiv.prodCongr U.2.equiv (Equiv.refl _)).trans
      (Equiv.prodAssoc K ↥(U : Set H) ↥(T : Set G))

end CorestrictionTransversal
end ContinuousCohomology
end
end
