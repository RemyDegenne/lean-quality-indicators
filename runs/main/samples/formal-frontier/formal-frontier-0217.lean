set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

namespace StableGL

@[simp]
theorem lift_stage (R : Type u) [Semiring R] {G : Type v} [Group G]
    (maps : ∀ n, GL (Fin n) R →* G)
    (compatible : ∀ n m (h : n ≤ m) (g : GL (Fin n) R),
      maps m (finStabilize R h g) = maps n g)
    (n : ℕ) (g : GL (Fin n) R) :
    lift R maps compatible (stage R n g) = maps n g := rfl

end StableGL
end Matrix.GeneralLinearGroup
end
