@[expose] public section

noncomputable section

namespace NumberField.InfinitePlace

open AbsoluteValue.Completion UniformSpace.Completion NumberField.ComplexEmbedding

variable {K : Type*} [Field K] (v : InfinitePlace K)

namespace Completion

@[simp] theorem algebraMap_apply (k : K) : algebraMap K v.Completion k = (k : v.Completion) := rfl

end Completion
end NumberField.InfinitePlace
end
end
