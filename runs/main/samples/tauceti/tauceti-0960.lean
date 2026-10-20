public section

namespace TauCeti

namespace Grid

variable {n : ℕ}

@[simp]
theorem card_cIco (a b : Fin n) :
    (cIco a b).card =
      if a = b then 0
      else if a.val < b.val then b.val - a.val else n - a.val + b.val := by
  by_cases hab : a = b
  · simp [hab]
  by_cases hlt : a.val < b.val
  · rw [cIco_eq_Ico_of_lt hlt]
    simp [hab, hlt, Fin.card_Ico]
  · have hgt : b.val < a.val :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun h => hab (Fin.val_inj.mp h.symm))
    rw [cIco_eq_Ici_union_Iio_of_lt hgt,
      Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_left]
        intro x hx hxb
        simp only [Finset.mem_Ici, Finset.mem_Iio, Fin.le_def, Fin.lt_def] at hx hxb
        omega)]
    simp [hab, hlt, Fin.card_Ici, Fin.card_Iio]

end Grid
end TauCeti
end
