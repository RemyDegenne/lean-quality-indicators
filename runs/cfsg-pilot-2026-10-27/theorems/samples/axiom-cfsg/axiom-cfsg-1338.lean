public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup Equiv

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

section Tables

variable {n : ℕ}

theorem card_support_eq_movedCount {T : Table} {g : Perm (Fin n)} (hT : Rep n T g) :
    g.support.card = movedCount n T := by
  classical
  have h1 : g.support.card = ∑ i : Fin n, if ap T i.val ≠ i.val then 1 else 0 := by
    rw [Equiv.Perm.support, Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hT i.val i.isLt
    rw [idx_of_lt _ i.isLt] at this
    simp only [Equiv.Perm.smul_def, Fin.eta] at this
    simp only [this, ne_eq, Fin.val_inj]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => if ap T i ≠ i then 1 else 0), ← Finset.card_filter,
    movedCount, List.countP_eq_length_filter]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  congr 1

end Tables
end CFSG.SeitzReduction.SporadicRefine
end
