public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender

open Subgroup

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {K : Type*} [Group K]

theorem relIndex_pCoreOf_sylow_psu {L T : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : oTwoQuot ↥L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F))
    (hT : IsSylowTwoOf T L) :
    (pCoreOf 2 L).relIndex T = (2 ^ n) ^ 3 := by
  obtain ⟨e', hBproj⟩ := CFSG.Quasithin.benderType_statedProj hn hF
  have hB : BenderType (oTwoQuot ↥L) n 3 e' := hBproj.of_mulEquiv e.symm
  have hT1' := isSylowTwoOf_map_pCoreQuot hT
  simpa using relIndex_pCoreOf_sylow (ψ := MonoidHom.id (oTwoQuot ↥L))
    (by intro x; exact ⟨x, rfl⟩)
    (by intro z hz; rw [MonoidHom.ker_id] at hz; rw [Subgroup.mem_bot] at hz; simp [hz])
    hB (by norm_num) hT hT1'

end CFSG.Quasithin.Stroth
end
