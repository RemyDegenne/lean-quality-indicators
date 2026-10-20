public section

open scoped TensorProduct

namespace GaloisDescent

universe u v w

variable {k : Type u} {L : Type v} {R : Type w}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [CommRing R] [Algebra k R]

@[simp] theorem reconstructionEquiv_tmul (P : Subalgebra L (L ⊗[k] R))
    (hP : IsStable P) (l : L) (d : descended P) :
    ((reconstructionEquiv P hP (l ⊗ₜ[k] d) : P) : L ⊗[k] R) =
      l ⊗ₜ[k] (d : R) := rfl

end GaloisDescent
end
