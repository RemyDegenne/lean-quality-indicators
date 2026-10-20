@[expose] public section

namespace BGS.Markoff

variable {E : Type*} [Field E] [Fintype E]

@[simp]
theorem mem_weightedNonparabolicBadOrderTraceSupport_iff
    {alpha beta : E} {Hleft : Subgroup Eˣ} {orders : Finset ℕ}
    {rightSubgroup : ℕ → Subgroup Eˣ} {hleft : Hleft} :
    hleft ∈ weightedNonparabolicBadOrderTraceSupport
        alpha beta Hleft orders rightSubgroup ↔
      ∃ d ∈ orders, ∃ hright : rightSubgroup d,
        weightedSplitTorusTrace alpha beta hleft =
            splitTorusTrace hright ∧
          ((hright : Eˣ) ^ 2) ≠ 1 := by
  classical
  simp [weightedNonparabolicBadOrderTraceSupport]

end BGS.Markoff
end
