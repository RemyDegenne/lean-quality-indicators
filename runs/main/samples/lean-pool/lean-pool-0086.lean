@[expose] public section

noncomputable section

namespace AVenhance.Infra.Construction

theorem section2Scales_canonical {β : ℝ} (I : Ingredients β) :
    Section2Scales I (section2Radius I) (section2Amplitude I) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro m
    rfl
  · intro m
    rfl

end AVenhance.Infra.Construction
end
end
