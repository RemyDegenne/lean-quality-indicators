@[expose] public section

open Set

open Filter hiding Realizer

open scoped Topology

variable {α : Type*} {β : Type*} {σ : Type*} {τ : Type*}

open Ctop

namespace Ctop.Realizer

variable [TopologicalSpace α]

/-- A realizer of the neighborhood of a point. -/
protected def nhds (F : Realizer α) (a : α) : (𝓝 a).Realizer :=
  ⟨{ s : F.σ // a ∈ F.F s },
    { f := fun s ↦ F.F s.1
      pt := ⟨_, F.F.top_mem a⟩
      inf := fun ⟨x, h₁⟩ ⟨y, h₂⟩ ↦ ⟨_, F.F.inter_mem x y a ⟨h₁, h₂⟩⟩
      inf_le_left := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h ↦ (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).1
      inf_le_right := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h ↦ (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).2 },
    filter_eq <|
      Set.ext fun _x ↦
        ⟨fun ⟨⟨_s, as⟩, h⟩ ↦ mem_nhds_iff.2 ⟨_, h, F.isOpen _, as⟩, fun h ↦
          let ⟨s, h, as⟩ := F.mem_nhds.1 h
          ⟨⟨s, h⟩, as⟩⟩⟩

end Ctop.Realizer
end
