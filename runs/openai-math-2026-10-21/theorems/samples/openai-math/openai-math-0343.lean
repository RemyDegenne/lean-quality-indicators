namespace OAI

namespace KadisonKastler

open MeasureTheory Filter

open scoped Topology BoundedContinuousFunction

noncomputable section

variable {D H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [MeasurableSpace D] (μ : Measure D)

namespace WeakOperatorRepresentative

variable {μ}

@[simp]
theorem eval_star (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (star F) x = star (eval F x) := rfl

end WeakOperatorRepresentative
end
end KadisonKastler
end OAI
