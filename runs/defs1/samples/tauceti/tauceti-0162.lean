public noncomputable section

open scoped NNReal

open unitInterval MulOpposite

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace MooreReplacement

namespace Fiber

variable {p : C(E, B)} {b : B}

/-- The underlying pair of a point of the fibre. -/
def val (x : Fiber p b) : MooreReplacement p :=
  Subtype.val x

end Fiber
end MooreReplacement
end TauCeti
end
