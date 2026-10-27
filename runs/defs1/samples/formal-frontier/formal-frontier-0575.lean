set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uR uS uT

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
  {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- Elementary generators with coefficients in `I`, viewed as members of `E(R)`. -/
def relativeElementaryGenerators (I : TwoSidedIdeal R) :
    Set (elementarySubgroup ι R) :=
  {g | ∃ i j : ι, ∃ hij : i ≠ j, ∃ a : R, a ∈ I ∧
    g = (⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩ :
      elementarySubgroup ι R)}

end Matrix.GeneralLinearGroup
end
