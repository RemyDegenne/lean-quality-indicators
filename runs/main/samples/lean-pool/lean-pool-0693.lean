@[expose] public section

namespace UnrestrictedBooleanMul

namespace N4

noncomputable section

theorem secondJetFeedback_not_rankOne (α β : F₂) :
    ¬ HankelRankLEOne (secondJetFeedbackCoeff α β) := by
  intro h
  have hm := h (0 : Fin 4) 2 2 0
  simp [hankelMatrix, secondJetFeedbackCoeff, targetBasis, Pi.basisFun] at hm

end
end N4
end UnrestrictedBooleanMul
end
