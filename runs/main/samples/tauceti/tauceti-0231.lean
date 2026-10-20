public section

noncomputable section

open Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] [T2Space B] {p : E → B}
  (C : Set B) [CWComplex C] [RelCWComplex.Finite C]
  (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))

include hp hfin

theorem cwEulerChar_preimage_of_card_fiber {d : ℕ} (hd : ∀ b ∈ C, Nat.card ↥(p ⁻¹' {b}) = d) :
    letI := cwComplexPreimage C hp
    cwEulerChar (p ⁻¹' C) = d * cwEulerChar C := by
  let := cwComplexPreimage C hp
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅))
  have hN' (n : ℕ) (hn : N ≤ n) : IsEmpty (cell (p ⁻¹' C) n) :=
    (cellPreimageEquiv C hp n).isEmpty_congr.2 ⟨fun c ↦ (hN n hn).false c.1⟩
  rw [cwEulerChar_eq_sum_range _ hN', cwEulerChar_eq_sum_range _ hN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [nat_card_cell_preimage_of_card_fiber C hp hfin hd, Nat.cast_mul]
  ring

end TauCeti
end
end
