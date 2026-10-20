public noncomputable section

open scoped NNReal

open unitInterval MulOpposite

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace MooreReplacement

namespace Fiber

variable {p : C(E, B)} {b : B}

@[simp]
theorem act_one (x : Fiber p b) : x.act 1 = x :=
  ext (MooreReplacement.ext (by simp) (by simp))

end Fiber
end MooreReplacement
end TauCeti
end
