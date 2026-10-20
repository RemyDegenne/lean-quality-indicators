@[expose] public section

open Rat Real

namespace Irrational

variable (q : ℚ) {x y : ℝ}

theorem of_add_ratCast : Irrational (x + q) → Irrational x :=
  add_comm (↑q) x ▸ of_ratCast_add q

end Irrational
end
