public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β ι : Type*}

/-- The left shift on one-sided path space. -/
@[expose]
def shift (α : Type*) (x : ℕ → α) : ℕ → α :=
  fun n => x (n + 1)

end Probability
end TauCeti
end
end
