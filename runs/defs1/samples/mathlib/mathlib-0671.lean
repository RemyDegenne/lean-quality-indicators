@[expose] public section

open Finset Function

variable {α : Type*}

namespace Finpartition

section DistribLattice

variable [DistribLattice α] [OrderBot α] [DecidableEq α] {a b c : α}

/-- Restrict a partition of `a` to `b` where `b ≤ a` by intersecting each part with `b`. -/
def restrict (P : Finpartition a) (hb : b ≤ a) : Finpartition b where
  parts := (P.parts.image (· ⊓ b)).erase ⊥
  supIndep := supIndep_iff_pairwiseDisjoint.mpr fun x hx y hy hxy => by
    simp only [coe_erase, coe_image, Set.mem_sdiff, Set.mem_image, Set.mem_singleton_iff] at hx hy
    obtain ⟨⟨px, hpx, rfl⟩, _⟩ := hx
    obtain ⟨⟨py, hpy, rfl⟩, _⟩ := hy
    simpa [Function.onFun, id_eq]
      using (P.disjoint hpx hpy fun h => hxy (h ▸ rfl)).mono inf_le_left inf_le_left
  sup_parts := by
    simp only [sup_erase_bot, sup_image, Function.id_comp, (sup_inf_distrib_right ..).symm]
    have : P.parts.sup (fun x => x) = a := P.sup_parts
    rw [this, inf_eq_right.mpr hb]
  bot_notMem := notMem_erase _ _

end DistribLattice
end Finpartition
end
