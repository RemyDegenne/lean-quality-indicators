public section

namespace TauCeti.TerminalCut

open Finset

variable {V W K : Type*}

theorem minimumValue_map [Finite V] [Finite W] [LinearOrder K] (e : V ≃ W)
    {f : Finset V → K} {g : Finset W → K}
    (hfg : ∀ S, g (S.map e.toEmbedding) = f S) {A B : Finset V}
    (hAB : Disjoint A B) :
    minimumValue g ((Finset.disjoint_map e.toEmbedding).mpr hAB) = minimumValue f hAB := by
  obtain ⟨S, hS⟩ := exists_minimum f hAB
  have hm := (isMinimum_map_iff e hfg).mpr hS
  rw [← ((isMinimum_iff_value_eq g _).mp hm).2,
    ← ((isMinimum_iff_value_eq f hAB).mp hS).2, hfg]

end TauCeti.TerminalCut
end
