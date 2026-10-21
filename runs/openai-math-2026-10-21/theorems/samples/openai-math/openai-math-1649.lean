namespace OAI

open Set MeasureTheory

open scoped RealInnerProductSpace Pointwise

namespace Paper092

theorem projectionBody_isCompact {n : ℕ} (K : Set (Euclidean n)) :
    IsCompact (projectionBody K) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨projectionBody_isClosed K, isBounded_iff_forall_norm_le.mpr ?_⟩
  exact ⟨_, fun _ hy => projectionBody_norm_le K hy⟩

end Paper092
end OAI
