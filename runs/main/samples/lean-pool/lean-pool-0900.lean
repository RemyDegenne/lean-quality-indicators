@[expose] public section

namespace TauCeti

namespace DavisKahan.Sylvester

open TauCeti.DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open MeasureTheory Set Filter

open scoped InnerProductSpace BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem measurable_chosenFiniteStepSymbol {n : ℕ}
    (cell : Fin n → Set ℝ) (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Set.PairwiseDisjoint Set.univ cell) (rep : Fin n → ℝ) :
    Measurable (chosenFiniteStepSymbol cell rep) := by
  classical
  have hstep : Measurable (fun x : ℝ => ∑ i, (cell i).indicator (fun _ => rep i) x) :=
    Finset.measurable_sum _ fun i _ => measurable_const.indicator (hcell i)
  have heq : chosenFiniteStepSymbol cell rep =
      (⋃ i, cell i).piecewise
        (fun x => ∑ i, (cell i).indicator (fun _ => rep i) x) (fun x => x) := by
    funext x
    by_cases hx : x ∈ ⋃ i, cell i
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      have hex : ∃ j, x ∈ cell j := ⟨i, hxi⟩
      have hxj : x ∈ cell (Classical.choose hex) := Classical.choose_spec hex
      have hji : Classical.choose hex = i := by
        by_contra hne
        exact Set.disjoint_left.mp
          (hdisj (Set.mem_univ (Classical.choose hex)) (Set.mem_univ i) hne) hxj hxi
      rw [chosenFiniteStepSymbol, dite_eq_left hex, hji, Finset.sum_eq_single i]
      · rw [Set.indicator_of_mem hxi]
      · intro k _ hki
        have hxk : x ∉ cell k := fun hxk =>
          Set.disjoint_left.mp
            (hdisj (Set.mem_univ k) (Set.mem_univ i) hki) hxk hxi
        rw [Set.indicator_of_notMem hxk]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      have hnex : ¬ ∃ i, x ∈ cell i := fun ⟨i, hxi⟩ =>
        hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)
      rw [chosenFiniteStepSymbol, dite_eq_right hnex]
  rw [heq]
  exact Measurable.piecewise (MeasurableSet.iUnion hcell) hstep measurable_id

end
end DavisKahan.Sylvester
end TauCeti
end
