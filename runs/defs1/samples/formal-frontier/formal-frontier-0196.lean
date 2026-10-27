set_option warningAsError true

@[expose] public section

noncomputable section

universe uA uB uC uQ uN uE uE'

namespace TopologicalPowerQuotient

/-- The topological closure of the subgroup of `n`-th powers. -/
def closedPowers (A : Type uA) [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] (n : ℕ) : Subgroup A :=
  (powers A n).topologicalClosure

end TopologicalPowerQuotient
end
end
