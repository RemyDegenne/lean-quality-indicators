namespace OAI

namespace EditApproximation

namespace BinaryFraction

attribute [local irreducible] seedGridSpacingWithWork gridStateBoxWithWork filterWithWork
  initialCenterGuardWithWork initialScaleGuardWithWork

theorem initialCentersWithWork_bounds {n : ℕ} (N P Amax B : ℕ)
    (A : BinaryFraction) (U : TargetInterval n → ℕ) (q : TargetInterval n)
    (hB : 8 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hn : Nat.size n ≤ B) (hU : ∀ r, Nat.size (U r) ≤ B) (hAb : A.width ≤ B)
    (hA : 1 ≤ A.value) (hmax : A.value ≤ Amax) :
    (initialCentersWithWork N P A U q).1.length ≤ (B + 1) * (64 * Amax ^ 2 * P + 2) ^ 2 ∧
      (initialCentersWithWork N P A U q).2 ≤ initialCentersBitBudget P Amax B := by
  let scales := dyadicScalesWithWork N
  let active := filterWithWork (fun b => initialScaleGuardWithWork (U q) b A) scales.1
  let callback := fun b =>
    let spacing := seedGridSpacingWithWork b P
    let points := gridStateBoxWithWork n (bitWordValue spacing.1) (U q) q.lo q.hi
    let selected := filterWithWork (fun r => initialCenterGuardWithWork b (U r) A) points.1
    (selected.1, spacing.2 + points.2 + selected.2 + 2)
  let L := 64 * Amax ^ 2 * P + 2
  have hscales : scales.1.length ≤ B + 1 := by
    simp only [scales, dyadicScalesWithWork_value, dyadicScales_length_bits, Nat.size_eq_bits_len]
    omega
  have hactive : active.1.length ≤ B + 1 := by
    exact (show active.1.length ≤ scales.1.length by
      rw [filterWithWork_value]; exact List.length_filter_le _ _).trans hscales
  have hmembers (b : ℕ) (hb : b ∈ active.1) :
      b ∈ dyadicScales N ∧ (initialScaleGuardWithWork (U q) b A).1 = true := by
    have hm := List.mem_filter.mp (show b ∈ scales.1.filter
      (fun b => (initialScaleGuardWithWork (U q) b A).1) by simpa only [active, filterWithWork_value] using hb)
    exact ⟨by simpa only [scales, dyadicScalesWithWork_value] using hm.1, hm.2⟩
  have hcallback (b : ℕ) (hb : b ∈ active.1) :
      (callback b).2 ≤ initialGridScaleBitBudget P Amax B ∧ (callback b).1.length ≤ L ^ 2 :=
    initialGridScale_bounds N P Amax B b A U q hB hP hN hPb hn hU hAb hA hmax
      (hmembers b hb).1 (hmembers b hb).2
  have hg := filterWithWork_cost (fun b => initialScaleGuardWithWork (U q) b A)
    scales.1 (initialScaleGuardBitBudget (B + 4)) (by
      intro b hb
      have hmem : b ∈ dyadicScales N := by simpa only [scales, dyadicScalesWithWork_value] using hb
      have hbb := dyadicScale_size N B b hN hmem
      exact initialScaleGuardWithWork_cost (U q) b (B + 4) A (by omega)
        (by have := hU q; omega) (by omega) (by omega))
  have hgc := hg.trans (Nat.mul_le_mul_right _ hscales)
  have hc := arithmeticFlatMapWithWork_cost callback active.1 (initialGridScaleBitBudget P Amax B)
    (L ^ 2) (fun b hb => (hcallback b hb).1) (fun b hb => (hcallback b hb).2)
  have hcc := hc.trans (Nat.mul_le_mul_right _ hactive)
  have hs := dyadicScalesWithWork_cost N
  have hsc : scales.2 ≤ (B + 1) * (B + 9) + 2 := by
    exact hs.trans (Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 2)
  constructor
  · rw [show (initialCentersWithWork N P A U q).1 = active.1.flatMap (fun b => (callback b).1) by
      exact arithmeticFlatMapWithWork_value callback active.1]
    exact (list_flatMap_length_le _ _ _ (fun b hb => (hcallback b hb).2)).trans
      (Nat.mul_le_mul_right _ hactive)
  · change scales.2 + active.2 + (arithmeticFlatMapWithWork callback active.1).2 + 3 ≤ _
    change active.2 ≤ _ at hgc
    unfold initialCentersBitBudget
    dsimp only
    simp only [L] at hcc ⊢
    omega

end BinaryFraction
end EditApproximation
end OAI
