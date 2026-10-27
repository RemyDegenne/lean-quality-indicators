public section

open Finset

namespace TauCeti

variable {Γ Γ' : Type*} [Preorder Γ] [Preorder Γ']

namespace FiniteSlopeData

variable (d : FiniteSlopeData ℝ)

/-- The finite slope data of a convex height sequence whose finite domain is `[l, l + k]`. -/
noncomputable def ofIsConvexSeq {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h) {l k : ℕ}
    (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n ∧ n ≤ l + k) : FiniteSlopeData ℝ where
  start := l
  initialHeight := (h l).untop₀
  length := k
  slope i := unitSlope h (l + i)
  monotone i j hij := by
    have hi := i.2
    have hj := j.2
    have hij' : (i : ℕ) ≤ j := hij
    exact hh.monotoneOn
      (mem_finiteEdges.2 ⟨(hdom _).2 ⟨by omega, by omega⟩, (hdom _).2 ⟨by omega, by omega⟩⟩)
      (mem_finiteEdges.2 ⟨(hdom _).2 ⟨by omega, by omega⟩, (hdom _).2 ⟨by omega, by omega⟩⟩)
      (by omega)

end FiniteSlopeData
end TauCeti
end
