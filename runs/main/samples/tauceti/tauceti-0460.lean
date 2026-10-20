public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] (K L : PreAbstractSimplicialComplex ι) (σ : Finset ι)

variable {K L σ}

variable {ρ : Finset ι}

section IsCone

variable {v : ι}

theorem isCone_deletion (h : IsCone K v) (hσ : σ.Nonempty) (hv : v ∉ σ) :
    IsCone (deletion K σ) v where
  apex_mem := by
    refine mem_deletion.mpr ⟨h.apex_mem, fun hsub => ?_⟩
    rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl
    · exact hσ.ne_empty rfl
    · exact hv (Finset.mem_singleton_self v)
  insert_mem ω hω := by
    rw [mem_deletion] at hω ⊢
    exact ⟨h.insert_mem hω.1, fun hsub =>
      hω.2 ((Finset.subset_insert_iff_of_notMem hv).mp hsub)⟩

end IsCone
end PreAbstractSimplicialComplex
end
