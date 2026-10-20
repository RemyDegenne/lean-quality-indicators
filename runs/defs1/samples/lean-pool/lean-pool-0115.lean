@[expose] public section

namespace GKPCarry

open Nat

/-- The remaining language-avoidance statement for nonexceptional powers of
two.  This proposition is open. -/
def gkpBadCarryLanguageExclusion : Prop :=
  ∀ k : ℕ, 2 < k → k ≠ 6 → k ≠ 8 →
    badCarryLanguage (Nat.digits 3 (2 ^ k)) = false

end GKPCarry
end
