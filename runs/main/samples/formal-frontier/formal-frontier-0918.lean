set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uR uS uT

section MapBlocks

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
  {R : Type uR} {S : Type uS} [Ring R] [Ring S]

@[simp]
theorem mapRingHom_lowerUnit (f : R →+* S) (a : Matrix ι ι R) :
    mapRingHom f (lowerUnit a) = lowerUnit (f.mapMatrix a) := by
  apply Units.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases h : i = j <;> simp [mapRingHom, lowerUnit, h]

end MapBlocks
end Matrix.GeneralLinearGroup
end
