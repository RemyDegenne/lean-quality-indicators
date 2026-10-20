public section

open Filter Finset MeasurableSpace MeasureTheory Preorder ProbabilityTheory

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Measure

universe u

variable {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]

section CouplingChain

variable {Y : Type u} [MeasurableSpace Y]

theorem map_adjacent_chainMeasure_of_isCoupling [StandardBorelSpace Y] [Nonempty Y]
    {mu : ℕ → Measure Y} {pi : ℕ → Measure (Y × Y)}
    [∀ n, IsFiniteMeasure (pi n)]
    (hpi : ∀ n, IsCoupling (pi n) (mu n) (mu (n + 1))) (n : ℕ) :
    (chainMeasure (X := fun _ ↦ Y) pi).map (fun x ↦ (x n, x (n + 1))) = pi n :=
  map_adjacent_chainMeasure pi n
    (fun k _ ↦ by rw [(hpi k).snd_eq, (hpi (k + 1)).fst_eq])

end CouplingChain
end Measure
end TauCeti
end
