@[expose] public section

namespace Complexity

namespace TM

/-- Add a hardwired natural to one canonical binary work tape. -/
def binaryAddConstTM {n : ℕ} (idx : Fin n) : ℕ → TM n
  | 0 => skipTM
  | fixedValue + 1 =>
      seqTM (binaryAddConstTM idx fixedValue) (binarySuccTM idx)

end TM
end Complexity
end
