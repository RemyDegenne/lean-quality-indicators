@[expose] public section

noncomputable section

namespace NumberField.InfinitePlace

open AbsoluteValue.Completion UniformSpace.Completion NumberField.ComplexEmbedding

variable {K : Type*} [Field K] (v : InfinitePlace K)

namespace Completion

/-- `Completion.toCompletion` and `Completion.ofCompletion` as an equivalence. -/
@[simps]
def equivCompletion : v.Completion ≃ v.1.Completion where
  toFun := toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl

end Completion
end NumberField.InfinitePlace
end
end
