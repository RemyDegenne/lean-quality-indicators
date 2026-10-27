public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

namespace Setting

variable {a : X} {L W K : Subgroup X} (h : Setting X a L W K)

include h

theorem false_of_holtSimple_outcome
    (hMax : MaximalTwoComponentInputHe)
    (hout : (∃ M : Subgroup X, CFSG.IsStronglyEmbedded M) ∨
      ∃ n : ℕ, Odd n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) : False := by
  have : IsSimpleGroup X := h.simple
  obtain ⟨eL⟩ := h.held
  rcases hout with ⟨M, hM⟩ | ⟨n, -, ⟨e⟩⟩
  · obtain ⟨A, -, hAe, hA64, -⟩ := h.wGroup_eq
    obtain ⟨V, hVA, hV4⟩ := exists_le_card_four hAe.isPGroup (by omega)
    exact false_of_isStronglyEmbedded hM hV4 (fun v hv => by rw [pow_two]; exact hAe.2 v (hVA hv))
      h.orderOf_eq h.le_centralizer eL
  · exact false_of_mulEquiv_alternatingGroup e h.orderOf_eq h.le_centralizer
      (h.centralizer_le_normalizer hMax) h.isPComponent eL

end Setting
end CFSG.ComponentClassification.GrSLit.HeSN
end
