set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

open scoped commutatorElement

theorem mem_stableElementarySubgroup_iff (R : Type u) [Ring R]
    (g : StableGL R) :
    g ∈ stableElementarySubgroup R ↔
      ∃ n : ℕ, ∃ e : elementarySubgroup (Fin n) R, StableGL.stage R n e = g := by
  rw [stableElementarySubgroup,
    Subgroup.mem_iSup_of_directed (elementary_stage_directed R)]
  constructor
  · rintro ⟨n, ⟨e, he, rfl⟩⟩
    exact ⟨n, ⟨e, he⟩, rfl⟩
  · rintro ⟨n, ⟨e, he⟩, rfl⟩
    exact ⟨n, ⟨e, he, rfl⟩⟩

end Matrix.GeneralLinearGroup
end
