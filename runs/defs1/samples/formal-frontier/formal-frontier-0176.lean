@[expose] public section

universe u v w

namespace Valuation

variable {K : Type u} [Field K] {ι : Type v} {Γ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] (val : ι → Valuation K Γ₀)

/-- The canonical inclusion of the common valuation integers into one valuation ring. -/
def intersectionInclusion (i : ι) :
    intersectionSubring val →+* (val i).valuationSubring :=
  Subring.inclusion (show intersectionSubring val ≤ (val i).valuationSubring.toSubring from
    fun x hx => (mem_intersectionSubring_iff val x).mp hx i)

end Valuation
end
