@[expose] public section

open Set

open Filter hiding Realizer

open scoped Topology

variable {α : Type*} {β : Type*} {σ : Type*} {τ : Type*}

open Ctop

namespace Ctop.Realizer

variable [TopologicalSpace α]

/-- Replace the representation type of a `Ctop` realizer. -/
def ofEquiv (F : Realizer α) (E : F.σ ≃ τ) : Realizer α :=
  ⟨τ, F.F.ofEquiv E,
    ext' fun a s ↦
      F.mem_nhds.trans
        ⟨fun ⟨s, h⟩ ↦ ⟨E s, by simpa using h⟩, fun ⟨t, h⟩ ↦ ⟨E.symm t, by simpa using h⟩⟩⟩

end Ctop.Realizer
end
