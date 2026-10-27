public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Sporadic.Schreier

open CFSG.RankThree.PartTwo.KFacts.L34Max

theorem conjWord_check :
    ∀ p : Fin 3 × Fin 3, E0pow p ≠ 1 →
      ofN0 (conjWord p) * e0a = E0pow p * ofN0 (conjWord p) := by
  decide +kernel

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
end
