@[expose] public section

variable {R E F G : Type _} [CommSemiring R] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
  [Module R E] [Module R F] [Module R G]

open scoped TensorProduct

@[reducible, instance]
noncomputable def funTensorProductAssocHasCoe' {A : Type _} :
    Coe (E ⊗[R] (F ⊗[R] G) → A) ((E ⊗[R] F) ⊗[R] G → A)
    where coe f x := f x

end
