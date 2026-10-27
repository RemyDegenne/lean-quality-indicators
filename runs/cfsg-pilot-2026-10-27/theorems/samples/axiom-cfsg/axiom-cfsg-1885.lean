public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

open scoped Pointwise

section General

variable {G : Type} [Group G]

variable [Finite G]

theorem le_normalizer_inf {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_forall_conj_mem'
  intro x hx
  exact ⟨(Subgroup.mem_normalizer_iff.mp (hA hg) x).mp hx.1,
    (Subgroup.mem_normalizer_iff.mp (hB hg) x).mp hx.2⟩

end General
end CFSG.Quasithin.H13
end
