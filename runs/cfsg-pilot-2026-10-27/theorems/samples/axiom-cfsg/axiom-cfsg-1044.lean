public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem mul_expand_right (τ X : Mat6) (M : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    M * (lift4 τ + (2 : ZMod 4) • lift4 X) =
      M * lift4 τ + (2 : ZMod 4) • lift4 (M.map red4 * X) := by
  rw [mul_add, mul_smul_comm, two_smul_lift4_mul_right]

end CFSG.EvenSmallLie.OmegaEight.Chain
end
