namespace OAI

namespace Falconer

open scoped ContDiff

variable {X Y E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

attribute [instance] SmoothSeparation.finite

namespace SmoothSeparation

@[simp] theorem product_value (a : X → E → ℂ) (b : Y → E → ℂ)
    (ha : ∀ x, ContDiff ℝ ∞ (a x)) (hb : ∀ y, ContDiff ℝ ∞ (b y))
    (x : X) (y : Y) (z : E) : (product a b ha hb).value x y z = a x z*b y z := by
  change (∑ _i : Unit, a x z*b y z) = a x z*b y z
  simp

end SmoothSeparation
end Falconer
end OAI
