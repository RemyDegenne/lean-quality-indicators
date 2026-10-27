public section

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

open CFSG.OddTranspositions CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G]

variable {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

namespace Config

theorem z_not_mem_K₁ (hQ : Config D u w v z a K₁ S') : z ∉ K₁ := by
  intro hz
  obtain ⟨-, hz1, -⟩ := hQ.z_facts
  obtain ⟨eK⟩ := hQ.K₁_A5
  have hc : eK ⟨z, hz⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨m, rfl⟩ := eK.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hQ.K₁_comm m.2))
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot,
    MulEquiv.map_eq_one_iff] at hc
  exact hz1 (congrArg Subtype.val hc)

end Config
end CFSG.OddTranspositions.QZ
end
