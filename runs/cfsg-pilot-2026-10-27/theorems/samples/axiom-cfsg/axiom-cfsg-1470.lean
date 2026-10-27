public section

namespace CFSG.Quasithin.RuType.StUnique

open scoped MatrixGroups Matrix

theorem isFlag_flagAct (g : SL(3, ZMod 2)) {x : Vec × Vec} (hx : IsFlag x) :
    IsFlag (flagAct g x) := by
  obtain ⟨h1, h2, h3⟩ := hx
  have e := flagAct_inv_flagAct g x
  refine ⟨fun h => h1 ?_, fun h => h2 ?_, ?_⟩
  · rw [← e]
    show ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (flagAct g x).1 = 0
    rw [h, Matrix.mulVec_zero]
  · rw [← e]
    show (flagAct g x).2 ᵥ* ((g⁻¹⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0
    rw [h, Matrix.zero_vecMul]
  · show (x.2 ᵥ* ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) ⬝ᵥ
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x.1) = 0
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    exact h3

end CFSG.Quasithin.RuType.StUnique
end
