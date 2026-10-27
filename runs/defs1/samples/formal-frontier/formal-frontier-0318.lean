@[expose] public section

open IsLocalRing

namespace ValuationSubring

universe u

variable {K : Type u} [Field K]

/-- The canonical residue map from a composite valuation subring to its second
factor. -/
noncomputable def compositeResidue (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) : A.composite W →+* W :=
  ((residue A).comp ((A.composite W).inclusion A (A.composite_le W))).codRestrict W
    fun x ↦ (mem_composite.mp x.property).choose_spec

end ValuationSubring
end
