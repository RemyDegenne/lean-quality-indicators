set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uR uS uT

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
  {R : Type uR} {S : Type uS} [Ring R] [Ring S]

@[simp]
theorem mapElementarySubgroup_comp {T : Type uT} [Ring T]
    (f : R →+* S) (g : S →+* T) :
    mapElementarySubgroup (ι := ι) (g.comp f) =
      (mapElementarySubgroup g).comp (mapElementarySubgroup f) := by
  ext x i j
  simp

end Matrix.GeneralLinearGroup
end
