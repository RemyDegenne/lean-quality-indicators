public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup

variable {G : Type*} [Group G]

theorem conjugate_of_mem_normalizer {H : Subgroup G} {a : G}
    (ha : a ∈ normalizer (H : Set G)) : conjugate H a = H := by
  ext x
  rw [mem_conjugate_iff]
  exact ((mem_normalizer_iff.1 ha x).symm)

end CFSG.Quasithin.SteinbergBS
end
