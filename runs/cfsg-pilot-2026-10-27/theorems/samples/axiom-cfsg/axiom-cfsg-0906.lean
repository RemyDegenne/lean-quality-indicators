public section

open CFSG.Open

namespace CFSG.ComponentClassification.Layer

theorem perfect (G : Type*) [Group G] : Group.IsPerfect (subgroup G) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _) _
  apply sSup_le
  intro component hcomponent
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  rw [← Subgroup.commutator_eq_self (H := component)]
  exact Subgroup.commutator_mono (component_le hcomponent) (component_le hcomponent)

end CFSG.ComponentClassification.Layer
end
