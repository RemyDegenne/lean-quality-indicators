@[expose] public section

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm

open scoped Real Manifold MatrixGroups

variable {m : ℕ}

/-- The permutation of the orbit induced by `T`: rotation `some b ↦ some (b+1)`, `none` fixed. -/
def σT (m : ℕ) : Equiv.Perm (Option (ZMod m)) := Equiv.optionCongr (Equiv.addRight (1 : ZMod m))

end Chudnovsky
end
end
