public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN uP

namespace TauCeti

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace ReducedTensorWords

/-- Deconcatenation on words of one fixed length, summed over all nontrivial cuts. -/
noncomputable def deconcatenationComponent (n : {n : ℕ // 0 < n}) :
    TensorPower R n.1 M →ₗ[R] ReducedTensorWords R M ⊗[R] ReducedTensorWords R M :=
  ∑ i : Fin (n.1 - 1),
    TensorProduct.map
        (of R M ⟨i.1 + 1, by omega⟩)
        (of R M ⟨n.1 - (i.1 + 1), by omega⟩) ∘ₗ
      TensorPower.splitAt R M n.1 (i.1 + 1) (by omega)

end ReducedTensorWords
end TauCeti
end
