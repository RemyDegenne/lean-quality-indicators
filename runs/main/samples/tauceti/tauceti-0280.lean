public section

universe u

open Module

namespace TauCeti

theorem _root_.IsIdempotentElem.two_mul_finrank_fixedSubmodule {K : Type*} {W : Type u} [Ring K]
    [HasRankNullity.{u} K] [AddCommGroup W] [Module K W] {q : Module.End K W}
    (hq : IsIdempotentElem q) (e : q.fixedSubmodule ≃ₗ[K] LinearMap.ker q) :
    2 * finrank K q.fixedSubmodule = finrank K W := by
  -- For an idempotent, the range is exactly the submodule of fixed vectors.
  have hr : LinearMap.range q = q.fixedSubmodule := by
    ext x
    rw [LinearMap.IsIdempotentElem.mem_range_iff hq, LinearMap.mem_fixedSubmodule_iff]
  -- Rank-nullity for `q`, with its kernel replaced by the equivalent fixed submodule.
  have h : 2 * Module.rank K q.fixedSubmodule = Module.rank K W := by
    rw [two_mul, ← q.rank_range_add_rank_ker, hr, e.rank_eq]
  -- `finrank` is `Cardinal.toNat` of the rank, which is multiplicative, also on infinite ranks.
  rw [finrank, finrank, ← h, Cardinal.toNat_mul, Cardinal.toNat_ofNat]

end TauCeti
end
