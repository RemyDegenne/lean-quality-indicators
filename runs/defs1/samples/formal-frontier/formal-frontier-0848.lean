public section

open scoped TensorProduct

namespace SeparableClosureDescent

universe u v w x y

section Stage

variable {k : Type u} {L : Type v} {K : Type w} {R : Type x}
  [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
  [CommRing R] [Algebra k R]

/-- Scalar extension of the finite-stage inclusion, with codomain the original
embedded subalgebra. -/
@[expose] noncomputable def reconstructionMap (P : Subalgebra K (K ⊗[k] R)) :
    K ⊗[L] stage (k := k) (L := L) P →ₐ[K] P :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom K K P)
    (stageInclusion (k := k) (L := L) P)
    (fun _ _ => .all _ _)

end Stage
end SeparableClosureDescent
end
