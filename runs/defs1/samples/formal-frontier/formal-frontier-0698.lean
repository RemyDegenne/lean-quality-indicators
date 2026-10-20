set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uR uS uT

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
  {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The normal closure of the ideal-coefficient generators **inside** `E(R)`. -/
def relativeElementarySubgroup (I : TwoSidedIdeal R) :
    Subgroup (elementarySubgroup ι R) :=
  Subgroup.normalClosure (relativeElementaryGenerators (ι := ι) I)

end Matrix.GeneralLinearGroup
end
