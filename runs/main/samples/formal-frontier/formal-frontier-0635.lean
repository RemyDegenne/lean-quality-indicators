@[expose] public section

universe u v

namespace MonoidAlgebra

variable {K : Type u} [Semiring K] {α : Type v}

theorem freeMonoidAugmentation_single (w : FreeMonoid α) (k : K) :
    freeMonoidAugmentation K α (single w k) =
      k * FreeMonoid.lift (fun _ : α ↦ (0 : K)) w := by
  simp only [freeMonoidAugmentation, liftNCRingHom_single, RingHom.id_apply]

end MonoidAlgebra
end
