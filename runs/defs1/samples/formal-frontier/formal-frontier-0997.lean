set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {R : Type u} [Ring R]

variable {n : Type v} [Fintype n] [DecidableEq n]

/-- The general linear group of a two-sided ideal is canonically equivalent to
the corresponding ambient congruence subgroup. -/
noncomputable def idealGeneralLinearGroupEquivCongruence
    (I : TwoSidedIdeal R) :
    idealGeneralLinearGroup (n := n) I ≃*
      congruenceSubgroup (n := n) I :=
  MulEquiv.ofBijective (idealGeneralLinearGroupToCongruence (n := n) I)
    (idealGeneralLinearGroupToCongruence_bijective I)

end Matrix.GeneralLinearGroup
end
