@[expose] public section

open Function ENNReal NNReal Set

noncomputable section

namespace EReal

theorem natCast_ne_iff {m n : ℕ} : (m : EReal) ≠ (n : EReal) ↔ m ≠ n :=
  not_iff_not.2 natCast_eq_iff

end EReal
end
end
