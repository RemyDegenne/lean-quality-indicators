set_option warningAsError true

noncomputable section

public section

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

variable (k : Type u) (l : Type v) (A : Type w)
  [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]

/-- Applying any k-linear functional `f : l →ₗ[k] k` to the right factor gives an
A-linear map from `A ⊗[k] l` back to A. It evaluates `a ⊗ₜ[k] b` as
`a * algebraMap k A (f b)`; neither `f 1 = 1` nor multiplicativity is needed.
The definition is noncomputable and exposed for downstream simplification; the
pure-tensor calculation follows from its universal-property construction, not
from an advertised definitional equality. -/
@[expose]
def rightLinearMap (f : l →ₗ[k] k) : A ⊗[k] l →ₗ[A] A :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a ↦ a • ((Algebra.linearMap k A).comp f)
      map_add' := fun a b ↦ by simp [add_smul]
      map_smul' := fun a b ↦ by simp [mul_smul] }

end Algebra.TensorProduct
end
end
