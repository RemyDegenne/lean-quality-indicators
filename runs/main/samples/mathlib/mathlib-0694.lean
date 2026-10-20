@[expose] public section

open Set Filter Topology

variable {X Y : Type*}

namespace OnePoint

@[inherit_doc]
scoped notation "∞" => OnePoint.infty

variable [TopologicalSpace X]

variable {s : Set (OnePoint X)}

theorem hasBasis_nhds_infty :
    (𝓝 (∞ : OnePoint X)).HasBasis (fun s : Set X => IsClosed s ∧ IsCompact s) fun s =>
      (↑) '' sᶜ ∪ {∞} := by
  rw [nhds_infty_eq]
  exact (hasBasis_coclosedCompact.map _).sup_pure _

end OnePoint
end
