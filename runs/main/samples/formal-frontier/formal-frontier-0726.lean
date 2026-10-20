@[expose] public section

noncomputable section

universe u v w

namespace Subring

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    [IsReduced R]

theorem perfectionMap_iInf_range_iterateFrobenius :
    PerfectionMap p
      (⨅ n : ℕ, (iterateFrobenius R p n).range : Subring R).subtype := by
  refine PerfectionMap.mk' (Perfection.coeffFrobeniusRangesEquiv R p).symm ?_
  apply Perfection.hom_ext
  intro x
  change (x : R) = ((Perfection.coeffFrobeniusRangesEquiv R p)
    ((Perfection.coeffFrobeniusRangesEquiv R p).symm x) : R)
  exact (congrArg Subtype.val
    ((Perfection.coeffFrobeniusRangesEquiv R p).apply_symm_apply x)).symm

end Subring
end
end
