public section

namespace TauCeti

variable {k : ℕ}

/-- **The middle graph of a stack.** Two points `a` and `b` of the middle boundary of the stack
of `D₁` above `D₂` are adjacent when a cap of `D₁` or a cup of `D₂` joins them: an arc that
stays in the middle instead of running out to the outer boundary. -/
def MiddleAdj (D₁ D₂ : BrauerDiagram k) (a b : Fin k) : Prop :=
  D₁.val (Sum.inl a) = Sum.inl b ∨ D₂.val (Sum.inr a) = Sum.inr b

end TauCeti
end
