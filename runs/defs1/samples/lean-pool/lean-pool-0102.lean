@[expose] public section

namespace Complexity

namespace RAM

/-- Accumulated **logarithmic time** over a fuel-bounded run: the sum of the
    per-step logarithmic costs of the non-halted steps taken. -/
def logTimeUpto (P : Program) : ℕ → Cfg → ℕ
  | 0, _ => 0
  | fuel + 1, c => if Halted P c then 0 else stepLogCost P c + logTimeUpto P fuel (step P c)

end RAM
end Complexity
end
