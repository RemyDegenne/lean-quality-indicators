public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e

open CFSG.Open

section Thm4Rest

open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.GLTheoremB

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut autBar)

variable {G : Type} [Group G] [Finite G]

theorem not_sq_dvd_120 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 120 := by
  intro h
  have hle : p ≤ 10 := by have := Nat.le_of_dvd (by norm_num) h; nlinarith
  have key : ∀ r : ℕ, r ≤ 10 → r.Prime → r ≠ 2 → ¬ r ^ 2 ∣ 120 := by decide
  exact key p hle hp hp2 h

end Thm4Rest
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e
end
