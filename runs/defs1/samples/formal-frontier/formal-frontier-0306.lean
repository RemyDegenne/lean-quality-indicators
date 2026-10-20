@[expose] public section

noncomputable section

universe u v w

namespace Module.Free

variable (R : Type u) [Ring R]

/-- Every chosen direct summand of `ℕ →₀ R` is absorbed by `ℕ →₀ R`. -/
def prodNatFinsuppEquivOfSplit
    (V : Type v) (W : Type w)
    [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (split : (ℕ →₀ R) ≃ₗ[R] V × W) :
    (V × (ℕ →₀ R)) ≃ₗ[R] (ℕ →₀ R) :=
  prodEquivOfCountableSelfSum R (ℕ →₀ R) V W
    (natFinsuppCountableSelfSum R) split

end Module.Free
end
end
