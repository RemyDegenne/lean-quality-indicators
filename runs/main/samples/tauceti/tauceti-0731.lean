public section

noncomputable section

open NumberField NumberField.InfinitePlace Module

open scoped TensorProduct NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (L) (v : InfinitePlace K)

variable {L v}

@[simp]
theorem infiniteSemilocalHom_tmul (a : v.Completion) (x : L)
    (w : {w : InfinitePlace L // w.LiesOver v}) :
    infiniteSemilocalHom L v (a ⊗ₜ x) w =
      algebraMap v.Completion w.1.Completion a * algebraMap L w.1.Completion x := by
  simp [infiniteSemilocalHom]

end TauCeti.GlobalNumberFields
end
end
