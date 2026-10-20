@[expose] public section

open Function

open scoped Finset

universe u v

variable {η α ι κ : Type*}

namespace Combinatorics

namespace Line

variable {l : Line α ι} {i : ι} {a x : α}

@[simp] lemma toSubspaceUnit_isMono {C : (ι → α) → κ} : l.toSubspaceUnit.IsMono C ↔ l.IsMono C := by
  simp only [Subspace.IsMono, toSubspaceUnit_apply, IsMono]
  exact exists_congr fun c ↦ ⟨fun h a ↦ h fun _ ↦ a, fun h a ↦ h _⟩

end Line
end Combinatorics
end
