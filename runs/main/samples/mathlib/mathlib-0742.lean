@[expose] public section

noncomputable section

open ModularForm UpperHalfPlane Complex Matrix CongruenceSubgroup Set

open scoped MatrixGroups

namespace EisensteinSeries

variable (N r : ℕ) (a : Fin 2 → ZMod N)

section gammaSet_def

lemma gammaSet_one_eq (a : Fin 2 → ZMod 1) :
    gammaSet 1 r a = {v : Fin 2 → ℤ | (v 0).gcd (v 1) = r} := by
  simp [gammaSet, Subsingleton.eq_zero (α := Fin 2 → ZMod 1)]

end gammaSet_def
end EisensteinSeries
end
end
