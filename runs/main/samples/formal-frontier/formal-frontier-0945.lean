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
theorem indexTwoCharacter_zero_apply_one : b.indexTwoCharacter 0 (b 1) = 1 := by
  exact congrFun (b.lift.symm_apply_apply (indexTwoCoefficients 0)) 1

end FreeGroupBasis
end
