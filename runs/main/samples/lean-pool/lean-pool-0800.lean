universe u

@[expose] public noncomputable section

open IGame Set Pointwise

namespace ConwayGame

@[simp, norm_cast] theorem mk_ratCast (q : ℚ) : mk q = q := rfl

end ConwayGame
end
