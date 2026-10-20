set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

omit [IsTopologicalGroup G] in
lemma crossedMap_comp_mkQL (q : A ⟶ B) [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] :
    TopModuleCat.ofHom (crossedMap q) ≫
        TopModuleCat.ofHom (principalCocycles B).mkQL =
      TopModuleCat.ofHom (principalCocycles A).mkQL ≫
        TopModuleCat.ofHom (crossedQuotientMap q) := by
  ext f
  rfl

end ContinuousCohomology
end
