@[expose] public section

noncomputable section

open Set Submodule

namespace LinearMap

universe uR uI

variable {R : Type uR} [Semiring R] {ι : Type uI}

namespace CountableInvariantCoordinateFiltration

variable {p : (ι →₀ R) →ₗ[R] (ι →₀ R)}

theorem iUnion_through (F : CountableInvariantCoordinateFiltration p) :
    ⋃ i, F.through i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro i
  exact Set.mem_iUnion.mpr ⟨i, F.mem_through i⟩

end CountableInvariantCoordinateFiltration
end LinearMap
end
end
