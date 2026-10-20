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

theorem extensionMap_trans (z : L ⊗[k] R) :
    extensionMap (k := k) (L := L) (K := K) (R := R) z =
      extensionMap (k := k) (L := M) (K := K) (R := R)
        (extensionMap (k := k) (L := L) (K := M) (R := R) z) := by
  induction z with
  | tmul l r =>
      simp only [extensionMap_tmul]
      rw [IsScalarTower.algebraMap_apply L M K]
  | add a b ha hb => simp only [map_add, ha, hb]

end Tower
end SeparableClosureDescent
end
