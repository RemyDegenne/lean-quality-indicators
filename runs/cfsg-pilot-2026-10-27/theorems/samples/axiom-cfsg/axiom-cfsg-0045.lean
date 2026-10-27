public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Lifts Matrix

namespace SignCompat

theorem YU_conj_toGL_T (e : Parker) (b : C) :
    conjGL (YU e) (toGL ⟨0, b, 0⟩) = toGL (conjT e b) := by
  refine Units.ext ?_
  rw [conjGL_apply, Units.val_mul, Units.val_mul, coe_YU_inv, coe_YU, coe_toGL, coe_toGL]
  exact conj_eq_of_mul_eq e (qmatR_T_mul_Ymat e b)

end SignCompat
end CFSG.Monster.Visible
end
