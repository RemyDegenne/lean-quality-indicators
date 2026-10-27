public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

namespace BlockData

variable {X : Subgroup (MulAut W)} {I : Finset (Subgroup (MulAut W))}

theorem comm_of_normalizes (hI : BlockData X I) {c y : MulAut W}
    (hcI : ∀ L ∈ I, B1.conjAut c L = L) (hc3 : ∃ k : ℕ, c ^ 3 ^ k = 1)
    (hy : y ∈ ⨆ L ∈ I, L) (hy3 : ∃ m : ℕ, y ^ 3 ^ m = 1) : c * y = y * c := by
  obtain ⟨k, hk⟩ := hc3
  obtain ⟨m, hm⟩ := hy3
  have hcard : ∀ L ∈ I, Nat.card L = 6 := fun L hL =>
    (S1417.card_of_actsAsNaturalL2 (hI.natural L hL)).1
  have hD : (⨆ L ∈ I, oTwoUpper L) ≤ Subgroup.centralizer ({c} : Set (MulAut W)) := by
    refine iSup₂_le fun L hL x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (commute_of_mem_oTwoUpper (hcard L hL) (mem_normalizer_of_conjAut_eq (hcI L hL)) hk
      hx).eq
  have hsq : y ^ 2 ∈ ⨆ L ∈ I, oTwoUpper L :=
    sq_mem_iSup_oTwoUpper I
      (fun L hL _ hl => sq_mem_oTwoUpper_of_card_eq_six (hcard L hL) hl) hI.comm y hy
  obtain ⟨j, hj⟩ : Odd ((3 : ℕ) ^ m) := Odd.pow (by decide)
  have hyj : y * (y ^ 2) ^ j = 1 := by
    rw [← pow_mul, ← pow_succ', ← hj]
    exact hm
  have hyD : y ∈ ⨆ L ∈ I, oTwoUpper L := by
    rw [eq_inv_of_mul_eq_one_left hyj]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hsq j)
  exact Subgroup.mem_centralizer_iff.mp (hD hyD) c rfl

end BlockData
end CFSG.LocalAnalysis.RankThreeUC
end
