public section

open scoped TensorProduct

namespace SeparableClosureDescent

universe u v w x y

section Tower

variable {k : Type u} {L : Type v} {M : Type y} {K : Type w} {R : Type x}
  [Field k] [Field L] [Field M] [Field K]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  [Algebra k K] [Algebra L K] [Algebra M K]
  [IsScalarTower k L K] [IsScalarTower k M K] [IsScalarTower L M K]
  [CommRing R] [Algebra k R]

theorem stage_tower (P : Subalgebra K (K ⊗[k] R)) :
    stage (k := k) (L := L) P =
      stage (k := k) (L := L) (stage (k := k) (L := M) P) := by
  ext z
  change extensionMap (k := k) (L := L) (K := K) (R := R) z ∈ P ↔
    extensionMap (k := k) (L := M) (K := K) (R := R)
      (extensionMap (k := k) (L := L) (K := M) (R := R) z) ∈ P
  rw [extensionMap_trans (M := M)]

end Tower
end SeparableClosureDescent
end
