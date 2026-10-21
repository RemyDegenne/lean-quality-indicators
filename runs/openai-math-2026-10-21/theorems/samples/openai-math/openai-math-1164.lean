namespace OAI

namespace Erdos970

open scoped _root_.Erdos970

namespace NumberTheoryLean.PrimeSideSupport

open _root_.Set _root_.MeasureTheory

open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory

open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon

theorem terminal_weak {w ell S : ℝ} {z : Node} {ps : List ℕ}
    (hz : Valid z.side z.ratio) (hp : allowed w ell S z ps) (hne : ps ≠ []) :
    WeakRegular (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hpath⟩
    cases ps with
    | nil => exact weak_step hz hchild
    | cons q qs => exact ih (child_valid hz hchild) hpath (by simp)

end NumberTheoryLean.PrimeSideSupport
end Erdos970
end OAI
