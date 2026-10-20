@[expose] public section

open Finset

open Sundog.MatchingNPHard

namespace Sundog.ThreeDMReindex

variable {W X Y : Type*}

variable [Fintype W] [Fintype X] [Fintype Y]

variable [DecidableEq W] [DecidableEq X] [DecidableEq Y]

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype W] [Fintype X] [Fintype Y] [DecidableEq I] in
theorem threeDM_reindex (t : I → W × X × Y) :
    threeDMI t ↔
      ThreeDM (fun i : Fin (Fintype.card I) => t ((Fintype.equivFin I).symm i)) := by
  set e := Fintype.equivFin I with he
  unfold threeDMI ThreeDM
  constructor
  · rintro ⟨T, hW, hX, hY⟩
    refine ⟨T.map e.toEmbedding, ?_, ?_, ?_⟩
    · intro w
      rw [map_filter_card_eq e T (fun p => p.1) t w]; exact hW w
    · intro x
      rw [map_filter_card_eq e T (fun p => p.2.1) t x]; exact hX x
    · intro y
      rw [map_filter_card_eq e T (fun p => p.2.2) t y]; exact hY y
  · rintro ⟨T, hW, hX, hY⟩
    refine ⟨T.map e.symm.toEmbedding, ?_, ?_, ?_⟩
    · intro w
      have h := map_filter_card_eq e.symm T (fun p => p.1) (fun i => t (e.symm i)) w
      simp only [Equiv.symm_symm, Equiv.symm_apply_apply] at h
      rw [h]; exact hW w
    · intro x
      have h := map_filter_card_eq e.symm T (fun p => p.2.1) (fun i => t (e.symm i)) x
      simp only [Equiv.symm_symm, Equiv.symm_apply_apply] at h
      rw [h]; exact hX x
    · intro y
      have h := map_filter_card_eq e.symm T (fun p => p.2.2) (fun i => t (e.symm i)) y
      simp only [Equiv.symm_symm, Equiv.symm_apply_apply] at h
      rw [h]; exact hY y

end Sundog.ThreeDMReindex
end
