public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

section BoundedFlow

variable [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K]

section Ordered

variable [PartialOrder K] [IsOrderedAddMonoid K]

namespace Flow

variable {cap : Assignment Q K} {s t : V}

/-- The *augmentation* of an ordinary `s`–`t` flow `f` by an ordinary `s`–`t` flow `r` of its
residual network: the residual update of `f` by `r`. -/
def augment (f : Flow cap s t) (r : Flow (residualCapacity 0 cap f.toFun) s t) :
    Flow cap s t where
  toBoundedFlow := f.update r.toBoundedFlow
  excessAt_sink_nonneg := by
    rw [← BoundedFlow.val_def, BoundedFlow.val_update]
    exact add_nonneg f.val_nonneg r.val_nonneg

end Flow
end Ordered
end BoundedFlow
end TauCeti
end
