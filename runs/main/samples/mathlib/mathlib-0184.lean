@[expose] public section

open Set Filter Function Topology

noncomputable section

namespace TopologicalSpace

universe u

variable {α : Type u} {β : Type*} [t : TopologicalSpace α] {B : Set (Set α)} {s : Set α}

theorem isTopologicalBasis_of_subbasis_of_inter {r : Set (Set α)} (hsg : t = generateFrom r)
    (hsi : ∀ ⦃s⦄, s ∈ r → ∀ ⦃t⦄, t ∈ r → s ∩ t ∈ r) : IsTopologicalBasis (insert univ r) :=
  isTopologicalBasis_of_subbasis_of_finiteInter (by simpa using hsg) (FiniteInter.mk₂ hsi)

end TopologicalSpace
end
end
