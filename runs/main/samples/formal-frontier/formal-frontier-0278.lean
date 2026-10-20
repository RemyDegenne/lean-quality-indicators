@[expose] public section

universe u v w

open CategoryTheory ContRepresentation TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable [CompactSpace G]

theorem coind₁_positive_eq_zero (X : TopRep.{max v w} k G)
    [DiscreteTopology X] (m : ℕ)
    (a : continuousCohomology (m + 1) (TopRep.coind₁ X)) : a = 0 := by
  let F := TopRep.coind₁ X
  let C := TopRep.homogeneousCochains F
  obtain ⟨z, rfl⟩ := π_surjective F (m + 1) a
  have hboundary : C.iCycles (m + 1) =
      (C.iCycles (m + 1) ≫ coind₁Insert X m) ≫ C.d m (m + 1) := by
    have hhomotopy : coind₁Insert X m ≫ C.d m (m + 1) +
        C.d (m + 1) (m + 2) ≫ coind₁Insert X (m + 1) =
        𝟙 (C.X (m + 1)) := coind₁Insert_homotopy X m
    have h := congrArg (fun f : C.X (m + 1) ⟶ C.X (m + 1) =>
      C.iCycles (m + 1) ≫ f) hhomotopy
    simpa only [Preadditive.comp_add, ← CategoryTheory.Category.assoc,
      C.iCycles_d, CategoryTheory.Limits.zero_comp, add_zero,
      CategoryTheory.Category.comp_id] using h.symm
  have hfactor : (C.iCycles (m + 1) ≫ coind₁Insert X m) ≫
      C.toCycles m (m + 1) = 𝟙 (C.cycles (m + 1)) := by
    apply (cancel_mono (C.iCycles (m + 1))).mp
    calc
      ((C.iCycles (m + 1) ≫ coind₁Insert X m) ≫
          C.toCycles m (m + 1)) ≫ C.iCycles (m + 1) =
          (C.iCycles (m + 1) ≫ coind₁Insert X m) ≫ C.d m (m + 1) := by
            rw [CategoryTheory.Category.assoc, C.toCycles_i]
      _ = C.iCycles (m + 1) := hboundary.symm
      _ = 𝟙 (C.cycles (m + 1)) ≫ C.iCycles (m + 1) := by simp
  have hπzero : C.homologyπ (m + 1) = 0 := by
    calc
      C.homologyπ (m + 1) =
          ((C.iCycles (m + 1) ≫ coind₁Insert X m) ≫
            C.toCycles m (m + 1)) ≫ C.homologyπ (m + 1) := by
              rw [hfactor, CategoryTheory.Category.id_comp]
      _ = 0 := by
        rw [CategoryTheory.Category.assoc, C.toCycles_comp_homologyπ,
          CategoryTheory.Limits.comp_zero]
  change (C.homologyπ (m + 1)).hom z = 0
  rw [hπzero]
  rfl

end ContinuousCohomology
end
