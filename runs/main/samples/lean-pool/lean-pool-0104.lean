@[expose] public section

open Finset

namespace Nibble.AX1

variable {q : ℕ}

variable [Fact (Nat.Prime q)]

theorem triCells_inter_subsingleton {T T' : Finset (ZMod q)} {j j' : ZMod q}
    (hT : #T = 3) (hT' : #T' = 3) (hne : ¬ (T = T' ∧ j = j'))
    {c d : ZMod q × ZMod q} (hc : c ∈ triCells T j) (hc' : c ∈ triCells T' j')
    (hd : d ∈ triCells T j) (hd' : d ∈ triCells T' j') : c = d := by
  by_contra hcd
  simp only [triCells, mem_image, Prod.ext_iff] at hc hc' hd hd'
  obtain ⟨a, haT, ha1, ha2⟩ := hc
  obtain ⟨a', ha'T, ha1', ha2'⟩ := hc'
  obtain ⟨b, hbT, hb1, hb2⟩ := hd
  obtain ⟨b', hb'T, hb1', hb2'⟩ := hd'
  subst ha1; subst hb1; subst ha1'; subst hb1'
  have hab : c.1 ≠ d.1 := by
    intro h
    exact hcd (Prod.ext h (by rw [← ha2, ← hb2, h]))
  have hs : (∑ v ∈ T, v) = ∑ v ∈ T', v := by
    have e1 : j + triShift (∑ v ∈ T, v) c.1 = j' + triShift (∑ v ∈ T', v) c.1 := by
      have := ha2.trans ha2'.symm; simpa [triBlock] using this
    have e2 : j + triShift (∑ v ∈ T, v) d.1 = j' + triShift (∑ v ∈ T', v) d.1 := by
      have := hb2.trans hb2'.symm; simpa [triBlock] using this
    have e3 : triShift (∑ v ∈ T, v) d.1 - triShift (∑ v ∈ T, v) c.1
        = triShift (∑ v ∈ T', v) d.1 - triShift (∑ v ∈ T', v) c.1 := by
      linear_combination e2 - e1
    rw [triShift_diff, triShift_diff] at e3
    have hz : (d.1 - c.1) * ((∑ v ∈ T', v) - ∑ v ∈ T, v) = 0 := by linear_combination e3
    rcases mul_eq_zero.1 hz with h' | h'
    · exact absurd (sub_eq_zero.1 h').symm hab
    · exact (sub_eq_zero.1 h').symm
  have hj : j = j' := by
    have h := ha2.trans ha2'.symm
    simp only [triBlock, hs, add_right_cancel_iff] at h
    exact h
  obtain ⟨x, hTx, hxa, hxb⟩ := exists_third_of_card_three hT haT hbT hab
  obtain ⟨x', hTx', hxa', hxb'⟩ := exists_third_of_card_three hT' ha'T hb'T hab
  rw [hTx, hTx', sum_triple hab hxa hxb, sum_triple hab hxa' hxb'] at hs
  have hxx : x = x' := by linear_combination hs
  exact hne ⟨by rw [hTx, hTx', hxx], hj⟩

end Nibble.AX1
end
