@[expose] public section

namespace Bananas

open Utilities

theorem crossOneOff_firing_identity
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1)) (a b m r : ℕ)
    (ha : a ≤ B.length α) (hb : b = m * B.length β + r)
    (hr : r ≤ B.length β) :
    linearEquiv B.graph
      ((g : ℤ) • oneChip (rightEndpoint B) +
        (a : ℤ) • oneChip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) • oneChip
          (strandVertex B β ⟨B.length β - 1, by
            have := B.length_pos β; omega⟩))
      (((a : ℤ) - (m : ℤ) - 2) • oneChip (leftEndpoint B) +
        ((g : ℤ) + (m : ℤ) - (b : ℤ)) •
          oneChip (rightEndpoint B) +
        oneChip (strandVertex B α ⟨a, by omega⟩) +
        oneChip (strandVertex B β ⟨r, by omega⟩)) := by
  have hFirst := crossOneOff_first_mark_multiple B α a ha
  have hSecond := crossOneOff_second_mark_multiple B β b m r hb hr
  unfold linearEquiv at hFirst hSecond ⊢
  have h := (principalDivisors B.graph).sub_mem hFirst hSecond
  convert h using 1;
    ext z;
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply];
    ring

end Bananas
end
