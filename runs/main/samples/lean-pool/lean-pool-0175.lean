@[expose] public section

open Finset

namespace Utilities.Certificate.WindowProfile

open Utilities.Certificate

open Utilities

open SubdivisionGraph

namespace Data

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p}

theorem edgeDivergence_pathVertex (data : Data spec) (edge : Fin p)
    (probe : spec.PathPosition edge) :
    data.edgeDivergence edge (spec.pathVertex edge probe) =
      (if probe.val = data.start edge then data.slope edge else 0) -
        (if probe.val = data.stop edge then data.slope edge else 0) := by
  classical
  have hAt : probe.val ≤ spec.length edge := by
    have := probe.isLt
    omega
  have hLeftIff (offset : Fin (spec.length edge)) :
      spec.stepLeft edge offset = spec.pathVertex edge probe ↔
        offset.val = probe.val := by
    rw [← spec.pathVertex_stepLeftPosition edge offset]
    rw [spec.pathVertex_eq_iff_val_eq]
    rfl
  have hRightIff (offset : Fin (spec.length edge)) :
      spec.stepRight edge offset = spec.pathVertex edge probe ↔
        offset.val + 1 = probe.val := by
    rw [← spec.pathVertex_stepRightPosition edge offset]
    rw [spec.pathVertex_eq_iff_val_eq]
    rfl
  simp only [edgeDivergence]
  simp_rw [hLeftIff, hRightIff]
  rw [Finset.sum_add_distrib]
  have hLeftSum :
      (∑ offset : Fin (spec.length edge),
        if offset.val = probe.val then
          windowSlope (data.start edge) (data.stop edge)
            (data.slope edge) offset.val else 0) =
      if probe.val < spec.length edge then
        windowSlope (data.start edge) (data.stop edge)
          (data.slope edge) probe.val else 0 := by
    by_cases hBefore : probe.val < spec.length edge
    · let selected : Fin (spec.length edge) := ⟨probe.val, hBefore⟩
      calc
        (∑ offset : Fin (spec.length edge),
            if offset.val = probe.val then
              windowSlope (data.start edge) (data.stop edge)
                (data.slope edge) offset.val else 0) =
            (if selected.val = probe.val then
              windowSlope (data.start edge) (data.stop edge)
                (data.slope edge) selected.val else 0) := by
          apply Fintype.sum_eq_single selected
          intro other hOther
          rw [ite_eq_right]
          intro hValue
          apply hOther
          apply Fin.ext
          exact hValue
        _ = _ := by simp [selected, hBefore]
    · have hNever (offset : Fin (spec.length edge)) :
          offset.val ≠ probe.val := by
        intro hValue
        have := offset.isLt
        omega
      simp [hBefore, hNever]
  have hRightSum :
      (∑ offset : Fin (spec.length edge),
        if offset.val + 1 = probe.val then
          -windowSlope (data.start edge) (data.stop edge)
            (data.slope edge) offset.val else 0) =
      if 0 < probe.val then
        -windowSlope (data.start edge) (data.stop edge)
          (data.slope edge) (probe.val - 1) else 0 := by
    by_cases hPositive : 0 < probe.val
    · let selected : Fin (spec.length edge) :=
        ⟨probe.val - 1, by omega⟩
      have hSelected : selected.val + 1 = probe.val := by
        dsimp [selected]
        omega
      calc
        (∑ offset : Fin (spec.length edge),
            if offset.val + 1 = probe.val then
              -windowSlope (data.start edge) (data.stop edge)
                (data.slope edge) offset.val else 0) =
            (if selected.val + 1 = probe.val then
              -windowSlope (data.start edge) (data.stop edge)
                (data.slope edge) selected.val else 0) := by
          apply Fintype.sum_eq_single selected
          intro other hOther
          rw [ite_eq_right]
          intro hValue
          apply hOther
          apply Fin.ext
          dsimp [selected]
          omega
        _ = _ := by simp [hPositive, hSelected, selected]
    · have hNever (offset : Fin (spec.length edge)) :
          offset.val + 1 ≠ probe.val := by omega
      simp [hPositive, hNever]
  rw [hLeftSum, hRightSum]
  have hDivergence := windowSlope_divergence (slope := data.slope edge)
    (data.start_le_stop edge) (data.stop_le_length edge) hAt
  by_cases hPositive : 0 < probe.val
  · simpa [hPositive, sub_eq_add_neg] using hDivergence
  · simpa [hPositive, sub_eq_add_neg] using hDivergence

end Data
end Utilities.Certificate.WindowProfile
end
