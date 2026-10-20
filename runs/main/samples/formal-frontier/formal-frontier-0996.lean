@[expose] public section

universe u

namespace FreeGroupBasis

variable {G : Type u} [Group G]

local notation "indexTwoCoefficients" =>
  (![![Multiplicative.ofAdd 1, 1], ![1, Multiplicative.ofAdd 1],
    ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 1]] :
      Fin 3 → Fin 2 → Multiplicative (ZMod 2))

variable (b : FreeGroupBasis (Fin 2) G)

@[simp]
theorem indexTwoGenerators_zero_apply_zero : b.indexTwoGenerators 0 0 = b 0 ^ 2 := rfl

end FreeGroupBasis
end
