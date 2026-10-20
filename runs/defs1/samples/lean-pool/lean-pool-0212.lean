@[expose] public section

namespace Utilities.Subdivision.TrivalentExpansion

open Utilities

open Utilities.Certificate

open Utilities.Certificate.ExplicitPotential

open Utilities.Certificate.SubdivisionGraph

open Utilities.Certificate.DegenerateSpec

open Utilities.Certificate.ContractionForestCensusGeneral

open Utilities.Certificate.PseudocorePresentation

open Utilities.Subdivision.CoreExpansion

open Utilities.Subdivision.CoreExpansion.ExpansionData

open AtanasovRanganathan.Configurations

section ClosedFace

variable {n p : ℕ} (C : Core n p)

variable (hDeg : ∀ w : Fin n, 3 ≤ slotValence C w)

/-- The contracted closed face is the original positive subdivision. -/
noncomputable def closedContraction (small : Spec n p)
    (hCore : small.core = C)
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e) :
    DegSpec.Contraction (closedFace C hDeg small hLoop) small where
  vtx := fun w => compFold (data C hDeg).bigCore
    (data C hDeg).contractedSlots (firstVertex C hDeg w)
  vtx_rep := by
    intro w
    rw [closedFace_rep]
    exact compFold_idem _ _ _
  vtx_inj := by
    intro a b hab
    have hFib := (compFold_eq_iff_fib_eq (conditions C hDeg hLoop) _ _).mp hab
    simpa using hFib
  vtx_surj := by
    intro v
    refine ⟨(data C hDeg).fib v, ?_⟩
    rw [closedFace_rep]
    exact (compFold_eq_iff_fib_eq (conditions C hDeg hLoop) _ _).mpr (by simp)
  slot := fun j => eEquiv C hDeg (Sum.inr j)
  slot_inj := by
    intro a b hab
    exact Sum.inr.inj ((eEquiv C hDeg).injective hab)
  slot_surj := by
    intro e hPos
    obtain ⟨a, rfl⟩ := exists_slot C hDeg e
    cases a with
    | inl x =>
        change 0 < closedLength C hDeg small (eEquiv C hDeg (Sum.inl x)) at hPos
        simp at hPos
    | inr j =>
        exact ⟨j, rfl⟩
  length_eq := by
    intro j
    change small.length j = closedLength C hDeg small (eEquiv C hDeg (Sum.inr j))
    simp
  tail_eq := by
    intro j
    rw [closedFace_rep]
    exact (compFold_eq_iff_fib_eq (conditions C hDeg hLoop) _ _).mpr (by
      simp only [closedFace_core]
      rw [data_tail, data_fib_firstVertex, data_fib]
      simp [bigTail, hCore])
  head_eq := by
    intro j
    rw [closedFace_rep]
    exact (compFold_eq_iff_fib_eq (conditions C hDeg hLoop) _ _).mpr (by
      simp only [closedFace_core]
      rw [data_head, data_fib_firstVertex, data_fib]
      simp [bigHead, hCore])

end ClosedFace
end Utilities.Subdivision.TrivalentExpansion
end
