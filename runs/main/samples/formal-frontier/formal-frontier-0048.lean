@[expose] public section

noncomputable section

universe u

namespace Matrix

variable (ι : Type u) [Fintype ι] [DecidableEq ι] (R : Type u) [CommRing R]

@[simp] theorem diagonalUnitsHom_apply (d : ι → Rˣ) (i j : ι) :
    diagonalUnitsHom ι R d i j = if i = j then (d i : R) else 0 := by
  change (diagonal fun k => (d k : R)) i j = _
  exact diagonal_apply _ _ _

end Matrix
end
end
