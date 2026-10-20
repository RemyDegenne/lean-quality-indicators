@[expose] public section

open Nat

namespace CutAndProject

open GeometricProjection

lemma sorted_multiset_unit_add_N (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω)
    (u : (ZMod (α ^ 2 + β ^ 2))ˣ) (i : ℤ) :
    let N := (⌊ω * ↑α⌋ + ⌊ω * ↑β⌋ + 1).toNat
    let D := α ^ 2 + β ^ 2
    sortedMultisetUnit α β ω u (i + ↑N) = sortedMultisetUnit α β ω u i + ↑D := by
  intro N D
  dsimp only [sortedMultisetUnit]
  have hN : 0 < N := N_pos_concrete α β ω h_ω
  have hN_ne : (N : ℤ) ≠ 0 := by omega
  have h_mod : (i + (N : ℤ)) % (N : ℤ) = i % (N : ℤ) := by
    have hm1 : (i + (N : ℤ)) % (N : ℤ) =
        (i % (N : ℤ) + (N : ℤ) % (N : ℤ)) % (N : ℤ) :=
      Int.add_emod i (N : ℤ) (N : ℤ)
    have hm2 : (N : ℤ) % (N : ℤ) = 0 := Int.emod_self
    have hm3 : (i % (N : ℤ)) % (N : ℤ) = i % (N : ℤ) :=
      Int.emod_emod i (N : ℤ)
    rw [hm2, add_zero, hm3] at hm1; exact hm1
  have h_div : (i + (N : ℤ)) / (N : ℤ) = i / (N : ℤ) + 1 := by
    have hd1 : (i + (N : ℤ)) / (N : ℤ) =
        i / (N : ℤ) + (N : ℤ) / (N : ℤ) :=
      Int.add_ediv_of_dvd_right (dvd_refl (N : ℤ))
    have hd2 : (N : ℤ) / (N : ℤ) = 1 := Int.ediv_self hN_ne
    rw [hd2] at hd1; exact hd1
  rw [h_mod, h_div]; ring

end CutAndProject
end
