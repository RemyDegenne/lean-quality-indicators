public section

open scoped TensorProduct

namespace GaloisDescent

universe u v w

variable {k : Type u} {L : Type v} {R : Type w}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [CommRing R] [Algebra k R]

/-- Scalar extension of the inclusion of the descended subalgebra. -/
@[expose] noncomputable def scalarExtensionMap (P : Subalgebra L (L ⊗[k] R)) :
    L ⊗[k] descended P →ₐ[L] L ⊗[k] R :=
  Algebra.TensorProduct.map (AlgHom.id L L) (descended P).val

end GaloisDescent
end
