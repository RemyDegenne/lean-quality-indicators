@[expose] public section

universe u v w z

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

theorem unitsKernel_fst (r : (unitsReduce R).ker) : (r.1 : DualNumber R).fst = 1 := by
  have h := congrArg (fun t : Rˣ => (t : R)) r.property
  exact h

end Matrix.DualNumberKernels
end
