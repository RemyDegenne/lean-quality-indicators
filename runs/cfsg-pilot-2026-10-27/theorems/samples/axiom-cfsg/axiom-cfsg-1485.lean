public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem B1Ctx.mem_normalizer {I Iz K : Subgroup G} {z : G} (c : B1Ctx I Iz K z) :
    z ∈ Subgroup.normalizer (K : Set G) := by
  have h := Subgroup.normalizer_commutator_ge_left K (Subgroup.zpowers z)
  rw [c.hKz] at h
  have h2 := Subgroup.normalizer_commutator_ge_right K (Subgroup.zpowers z)
  rw [c.hKz] at h2
  exact h2 (Subgroup.mem_zpowers z)

end Main
end CFSG.Quasithin
end
