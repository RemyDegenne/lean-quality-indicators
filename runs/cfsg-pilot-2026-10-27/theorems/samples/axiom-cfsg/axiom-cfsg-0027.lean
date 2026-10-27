public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup

variable {G : Type*} [Group G]

theorem mem_normalizer_comap {H : Type*} [Group H] (ι : G →* H) {R : Subgroup H} {n : G}
    (hn : ι n ∈ normalizer (R : Set H)) :
    n ∈ normalizer ((R.comap ι : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  show ι h ∈ R ↔ ι (n * h * n⁻¹) ∈ R
  rw [map_mul, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp hn _

end TenNineOneThree
end CFSG.LocalAnalysis.RankThreeTheoremC
end
