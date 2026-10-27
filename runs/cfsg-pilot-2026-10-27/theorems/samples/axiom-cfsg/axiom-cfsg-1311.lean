public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Un

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem cf67CoreDeriv_U4_cover
    (hUD : ∀ {Y : Type} [Group Y] [Finite Y], LieModel Y .PSU 4 3 1 → CF67CoreDeriv Y 3)
    (hGA : CFSG.Open.GriessAllModelsStatement) {J : Type}
    [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) (hY : FU4 (J ⧸ center J)) {r : ℕ}
    (hr : r.Prime) (hr2 : Odd r) (hd : r ∣ Nat.card (center J)) :
    CF67CoreDeriv (J ⧸ center J) r := by
  obtain ⟨p, f, -, -, hp2, -, hLie⟩ := hY
  have hr2' : r ≠ 2 := by
    rintro rfl
    exact absurd hr2 (by decide)
  obtain ⟨rfl, rfl, rfl⟩ := U4_cover_odd hGA hJ hp2 hLie hr hr2' hd
  exact hUD hLie

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Un
end
