@[expose] public section

noncomputable section

open scoped unitInterval

namespace Circle

theorem loop_one_ne_one :
    FundamentalGroup.fromPath ⟦loop 1⟧ ≠ (1 : FundamentalGroup Circle 1) := by
  intro h
  have h' := congrArg fundamentalGroupEquivInt h
  rw [fundamentalGroupEquivInt_loop, map_one fundamentalGroupEquivInt] at h'
  exact (one_ne_zero : (1 : ℤ) ≠ 0) (congrArg Multiplicative.toAdd h')

end Circle
end
end
