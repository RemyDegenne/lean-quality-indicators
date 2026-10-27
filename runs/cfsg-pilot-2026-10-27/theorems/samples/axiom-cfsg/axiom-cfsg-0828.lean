public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggTBJ_reflAut_ofAdd (p : ℕ) [Fact p.Prime] {β : Fin 4 → ℤ}
    (h : ggTBJFun p β (ggTBJVec p β) = 2) (w : Fin 4 → ZMod p) :
    ggTBJReflAut p β (Multiplicative.ofAdd w) = Multiplicative.ofAdd (ggTBJRefl p β w) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [ggTBJReflAut_apply p h, toAdd_ofAdd, toAdd_ofAdd]
  rfl

end CFSG.StandardType
end
