set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

noncomputable section

namespace CorestrictionTransversal

variable {H : Subgroup G} (T : H.RightTransversal)

variable (X : TopRep.{max v w} k G)

omit [IsTopologicalGroup G] in
lemma crossed_one (f : continuousCrossedHom (TopRep.res H.subtype X)) :
    f.1 1 = 0 := by
  have h := f.2 1 1
  simpa using h

end CorestrictionTransversal
end
end ContinuousCohomology
end
