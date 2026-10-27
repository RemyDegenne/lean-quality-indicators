open Equiv

attribute [local instance] Subgroup.fintypeOfFinite

public section

namespace TauCeti

variable {α : Type*} [Fintype α] [DecidableEq α]

open scoped Classical in
/-- The conjugacy classes of the subgroup `G` whose members have full cycle type `mu`.

One `S_n`-cycle type can meet several `G`-classes, and can meet none, so the elements of `G` of a
prescribed cycle type are counted by a sum over this index set rather than by one class size. -/
noncomputable def _root_.Subgroup.classesOfFullCycleType (G : Subgroup (Equiv.Perm α))
    (mu : Multiset ℕ) : Finset (ConjClasses G) :=
  {C ∈ (Finset.univ : Finset (ConjClasses G)) | ∃ g : G, ConjClasses.mk g = C ∧
    (g : Equiv.Perm α).fullCycleType = mu}

end TauCeti
end
