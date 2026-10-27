@[expose] public section

namespace LeanModelChecking

/-- Infinite path, with an arbitrary starting level. -/
def DAG.path {Q} (G : DAG Q) (p : ℕ → Q) :=
  ∃ n, ∀ i, ((p i, n + i), p (i + 1)) ∈ G.E

end LeanModelChecking
end
