public section

noncomputable section

open CategoryTheory Limits Set Topology

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {A B : Set X}

namespace FundamentalGroupoid

open _root_.FundamentalGroupoid

section Glue

variable {D : Type*} [Category D]

variable (hCover : interior A ∪ interior B = univ) (FA : FundamentalGroupoid A ⥤ D)
  (FB : FundamentalGroupoid B ⥤ D)
  (h : map (ContinuousMap.inclusion inter_subset_left) ⋙ FA =
    map (ContinuousMap.inclusion inter_subset_right) ⋙ FB)

/-- **Gluing two functors out of fundamental groupoids.** If the interiors of `A` and `B` cover
`X`, and `FA` and `FB` are functors out of the fundamental groupoids of `A` and `B` which agree
on the fundamental groupoid of `A ∩ B`, this is the functor out of the fundamental groupoid of
`X` which restricts to `FA` and to `FB` (`map_subtypeVal_comp_glueTwo_left`,
`map_subtypeVal_comp_glueTwo_right`); it is the unique such functor (`eq_glueTwo`). -/
def glueTwo : FundamentalGroupoid X ⥤ D :=
  glue (exists_twoCover_mem_nhds hCover)
    (fun b ↦ (Bool.rec FB FA b : FundamentalGroupoid (twoCover A B b) ⥤ D))
    (twoCover_compatibility FA FB h)

end Glue
end FundamentalGroupoid
end TauCeti
end
end
