set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

namespace StableGL

/-- Lift a compatible family of group homomorphisms from finite ranks. -/
def lift (R : Type u) [Semiring R] {G : Type v} [Group G]
    (maps : ∀ n, GL (Fin n) R →* G)
    (compatible : ∀ n m (h : n ≤ m) (g : GL (Fin n) R),
      maps m (finStabilize R h g) = maps n g) : StableGL R →* G where
  toFun := DirectLimit.lift (finStabilizeSystem R) (fun n g => maps n g)
    (fun n m h g => (compatible n m h g).symm)
  map_one' := by
    exact DirectLimit.lift_one (f := finStabilizeSystem R) (fun n => maps n)
      (fun n m h g => (compatible n m h g).symm)
  map_mul' g h := by
    exact DirectLimit.lift_mul (f := finStabilizeSystem R) (fun n => maps n)
      (fun n m h x => (compatible n m h x).symm) g h

end StableGL
end Matrix.GeneralLinearGroup
end
