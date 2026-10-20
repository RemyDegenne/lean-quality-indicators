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

omit [IsTopologicalGroup G] in
lemma crossedTrans_comp_mkQL (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X] :
    TopModuleCat.ofHom (crossedTrans X H K) ≫
        TopModuleCat.ofHom
          (principalCocycles
            (TopRep.res K.subtype (TopRep.res H.subtype X))).mkQL =
      TopModuleCat.ofHom
          (principalCocycles
            (TopRep.res (OpenSubgroup.trans H K).subtype X)).mkQL ≫
        TopModuleCat.ofHom (crossedQuotientTrans X H K) := by
  ext f
  rfl

end CorestrictionTransversal
end ContinuousCohomology
end
end
