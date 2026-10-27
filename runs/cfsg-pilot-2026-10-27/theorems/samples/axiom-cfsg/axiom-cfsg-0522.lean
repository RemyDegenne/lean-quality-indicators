public section

namespace CFSG.ComponentClassification.Asc76X.Hall32

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76

open CFSG.ComponentClassification.Asc76X

open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_dihedral {T : Subgroup G} {v : G} {hvN : v ∈ normalizer (T : Set G)}
    {hv2 : v * v = 1} {x : G} : x ∈ dihedral T v hvN hv2 ↔ x ∈ T ∨ x * v ∈ T :=
  Iff.rfl

end CFSG.ComponentClassification.Asc76X.Hall32
end
