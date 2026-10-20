set_option autoImplicit false

set_option warningAsError true

public section

open CategoryTheory

noncomputable section

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace TopRep

omit [IsTopologicalGroup G] in
theorem jointlyContinuous_res_trans (H : OpenSubgroup G) (K : OpenSubgroup H)
    (X : TopRep.{w} k G) [JointlyContinuous X] :
    JointlyContinuous (res K.subtype (res H.subtype X)) :=
  jointlyContinuous_res_res_open H K X

end TopRep
end
end
