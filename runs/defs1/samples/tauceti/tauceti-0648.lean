public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {K : Type u}

variable {ι : Type*} [DecidableEq ι]

variable {n : ℕ}

section AddGroupWithOne

variable [AddGroupWithOne K]

/-- The ambient root matrix for the opposite short root `-εᵢ`. -/
def typeBShortNegativeRootMatrix (i : ι) :
    Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  single (.inl ()) (.inr (.inl i)) 1 - single (.inr (.inr i)) (.inl ()) 2

end AddGroupWithOne
end TauCeti
end
