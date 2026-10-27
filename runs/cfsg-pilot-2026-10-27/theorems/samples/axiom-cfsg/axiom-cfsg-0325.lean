public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open scoped Pointwise

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A]

section Space

variable (r : ℕ) (qA : QuadraticForm K A)

variable {r qA}

theorem polar_hypVec_tail (c : Fin r ⊕ Fin r) (a : A) :
    polar (quadTail r qA) (hypVec K A c) ((0, a) : (Fin r ⊕ Fin r → K) × A) = 0 := by
  rw [polar_comm, polar_hypVec]
  rfl

end Space
end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
end
