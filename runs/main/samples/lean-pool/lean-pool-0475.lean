@[expose] public section

open scoped BigOperators

namespace BooleanIsoperimetry

lemma cubeToNat_gShift_erase_max {n : ℕ} {x : Cube n} (hx : x.Nonempty) (h2 : 2 ≤ x.card) :
    cubeToNat (gShift x) =
      cubeToNat (gShift (x.erase (x.max' hx))) + 2 ^ ((x.max' hx : ℕ)) := by
  by_cases hmax : (x.max' hx) ∈ gShift x
  · rw [cubeToNat_erase]
    focus congr! 1
    · congr! 1
      unfold gShift
      grind +suggestions
    · assumption
  · exfalso
    have h_shift : gShift x = x.erase (x.min' hx) := dite_eq_left hx
    rw [h_shift, Finset.mem_erase] at hmax
    have h_mem : x.max' hx ∈ x := Finset.max'_mem x hx
    have h_eq : x.max' hx = x.min' hx := by tauto
    have h_card : x.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have h1 : a = x.min' hx := le_antisymm (h_eq ▸ Finset.le_max' x a ha) (Finset.min'_le x a ha)
      have h2 : b = x.min' hx := le_antisymm (h_eq ▸ Finset.le_max' x b hb) (Finset.min'_le x b hb)
      rw [h1, h2]
    omega

end BooleanIsoperimetry
end
