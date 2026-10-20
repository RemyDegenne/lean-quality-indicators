public section

open scoped Affine

variable {k V P ι : Type*}

namespace Affine.Triangle

section CommRing

variable [CommRing k] [NoZeroDivisors k] [AddCommGroup V] [Module k V] [AffineSpace V P]

lemma prod_eq_prod_one_sub_of_mem_line_point_lineMap {t : Triangle k P} {r : Fin 3 → k} {p' : P}
    (hp' : ∀ i : Fin 3, p' ∈
      line[k, t.points i, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i)]) :
    ∏ i, r i = ∏ i, (1 - r i) := by
  rcases subsingleton_or_nontrivial k
  · exact Subsingleton.elim _ _
  let w : ↑(Set.univ : Set (Fin 3)) → Fin 3 → k :=
    fun i ↦ Finset.affineCombinationLineMapWeights (i + 1) (i + 2) (r i)
  have hw : ∀ i, ∑ j, w i j = 1 := by simp [w]
  have hp'w : ∀ i : ↑(Set.univ : Set (Fin 3)),
      p' ∈ line[k, t.points i, Finset.univ.affineCombination k t.points (w i)] := by
    simpa [w] using hp'
  obtain ⟨w', hw', rfl, h⟩ :=
    t.independent.exists_affineCombination_eq_smul_eq_of_fintype (by simp) hw hp'w
  have h' : ∀ i : Fin 3, ∃ c : k, ∀ j ≠ i, c * w ⟨i, by simp⟩ j = w' j := by
    intro i
    obtain ⟨c, hc⟩ := h ⟨i, by simp⟩
    refine ⟨c, fun j hj ↦ ?_⟩
    simpa [hj] using hc j
  simp only [Fin.isValue, w] at h'
  let c : Fin 3 → k := fun i ↦ (h' i).choose
  have hc (i : Fin 3) : ∀ j : Fin 3, j ≠ i →
    c i * Finset.affineCombinationLineMapWeights (i + 1) (i + 2) (r i) j = w' j :=
      (h' i).choose_spec
  have hc1 (i : Fin 3) : c i * (1 - r i) = w' (i + 1) := by
    rw [← hc i (i + 1) (by simp)]
    simp
  have hc2 (i : Fin 3) : c i * r i = w' (i + 2) := by
    rw [← hc i (i + 2) (by simp)]
    simp
  have hcr : (∏ i, c i) * ∏ i, r i = (∏ i, c i) * ∏ i, (1 - r i) := by
    simp_rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun _ _ ↦ hc1 _),
      Finset.prod_congr rfl (fun _ _ ↦ hc2 _)]
    suffices ∏ i, (w' ∘ Equiv.addRight 2) i = ∏ i, (w' ∘ Equiv.addRight 1) i by
      simpa using this
    simp_rw [Finset.prod_comp_equiv]
    simp
  by_cases hc : ∏ i, c i = 0
  · rw [Finset.prod_eq_zero_iff] at hc
    obtain ⟨i, -, hi⟩ := hc
    have hw'i1 : w' (i + 1) = 0 := by simpa [hi] using (hc1 i).symm
    have hw'i2 : w' (i + 2) = 0 := by simpa [hi] using (hc2 i).symm
    have hw'i0 : w' i = 1 := by
      rw [← hw', Fin.sum_univ_three]
      fin_cases i <;> grind
    have hi1 : c (i + 1) * r (i + 1) = 1 := by simpa [add_assoc, hw'i0] using hc2 (i + 1)
    have hi1' : c (i + 1) * (1 - r (i + 1)) = 0 := by
     simpa [add_assoc, hw'i2] using hc1 (i + 1)
    have hci1 : c (i + 1) = 1 := by
      suffices c (i + 1) * (r (i + 1) + (1 - r (i + 1))) = 1 + 0 by simpa using this
      rw [mul_add, hi1, hi1']
    have hri1 : r (i + 1) = 1 := by simpa [hci1] using hi1
    have hi2 : c (i + 2) * (1 - r (i + 2)) = 1 := by simpa [add_assoc, hw'i0] using hc1 (i + 2)
    have hi2' : c (i + 2) * r (i + 2) = 0 := by simpa [add_assoc, hw'i1] using hc2 (i + 2)
    have hci2 : c (i + 2) = 1 := by
      suffices c (i + 2) * (r (i + 2) + (1 - r (i + 2))) = 0 + 1 by simpa using this
      rw [mul_add, hi2, hi2']
    have hri2 : r (i + 2) = 0 := by simpa [hci2] using hi2'
    rw [Finset.prod_eq_zero (by simp) hri2,
      Finset.prod_eq_zero (i := i + 1) (by simp) (by simp [hri1])]
  · exact mul_left_cancel₀ hc hcr

end CommRing
end Affine.Triangle
end
