namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

section

noncomputable section

open NumberField

open scoped BigOperators

noncomputable section

open MeasureTheory

open scoped Topology

noncomputable section

open MeasureTheory

open scoped Topology ENNReal

noncomputable section

open MeasureTheory NumberField

open scoped BigOperators

noncomputable section

open scoped BigOperators

open MeasureTheory

namespace WeakPinned.SmallFiber

open MeasureTheory Hierarchy

variable {P : Type u5} [Fintype P] [DecidableEq P]

lemma mass_as_sum (p : P → ℝ) (C : Finset P) :
    mass p C = ∑ y, if y ∈ C then p y else 0 := by
  classical
  simp [mass]

end WeakPinned.SmallFiber
end
end
end
end
end
end
end OAI
