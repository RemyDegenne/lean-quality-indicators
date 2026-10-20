public noncomputable section

open scoped NNReal

open unitInterval MulOpposite

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace MooreReplacement

namespace Fiber

variable {p : C(E, B)} {b : B}

@[ext]
theorem ext {x y : Fiber p b} (h : x.val = y.val) : x = y :=
  Subtype.ext h

end Fiber
end MooreReplacement
end TauCeti
end
