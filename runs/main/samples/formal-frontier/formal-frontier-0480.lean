@[expose] public section

noncomputable section

open Set Submodule

namespace LinearMap

universe uR uI

variable {R : Type uR} [Semiring R] {ι : Type uI}

namespace CountableInvariantCoordinateFiltration

variable {p : (ι →₀ R) →ₗ[R] (ι →₀ R)}

theorem before_eq_iUnion_through
    (F : CountableInvariantCoordinateFiltration p) (i : ι) :
    F.before i = ⋃ j, ⋃ (_ : F.r j i), F.through j := by
  let _ := F.isWellOrder
  ext x
  constructor
  · intro hx
    rw [before] at hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hji, hx⟩ := Set.mem_iUnion.mp hj
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji,
      Set.mem_union_right _ hx⟩⟩
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hji, hx⟩ := Set.mem_iUnion.mp hj
    exact F.through_subset_before_of_rel hji hx

end CountableInvariantCoordinateFiltration
end LinearMap
end
end
