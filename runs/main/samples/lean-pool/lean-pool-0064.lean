@[expose] public section

namespace Connes

namespace PaperChartOrbits

open Construction

open Construction.PaperKernel

open PaperFiniteCharts

noncomputable section

theorem chartSquare_in_orbit (N : ℕ) (s : Fin 3)
    (f h : Fin N → F) :
    ∃ g : SpecialLinear.SL3,
      sl3CAction g (PaperKernel.diagonal (basisVector 0)) =
        chartSquare N (s, f, h) := by
  obtain ⟨g, hg⟩ := chartPoint_in_orbit N s f h
  refine ⟨g, ?_⟩
  rw [sl3CAction_diagonal, hg]
  rfl

end
end PaperChartOrbits
end Connes
end
