@[expose] public section

variable {α β ι R M : Type*} (f : α → β) (g : β → ι) [AddCommMonoid M]

open Set Filter

namespace Filter

/-- The class of functions `f` such that `Tendsto f cofinite cofinite`, it is equivalent to
`f` having finite fibers, see `Filter.tendstoCofinite_iff_finite_preimage_singleton`. -/
@[mk_iff] class TendstoCofinite (f : α → β) : Prop where
  tendsto_cofinite (f) : Tendsto f cofinite cofinite

end Filter
end
