@[expose] public section

open CategoryTheory Function Set

open CategoryTheory.Limits

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem primewisePadicGenerator_isTopologicalGenerator :
    IsTopologicalGenerator primewisePadic.{u} primewisePadicGenerator := by
  rw [IsTopologicalGenerator]
  rw [show (fun n : ℤ ↦ primewisePadicGenerator.{u} ^ n) =
      primewisePadicDiagonal.{u} by
    funext n
    funext p
    exact primewisePadicGenerator_zpow n p]
  exact denseRange_primewisePadicDiagonal

end ProfiniteGrp
end
