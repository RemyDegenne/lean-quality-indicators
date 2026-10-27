public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess Matrix

open scoped symmDiff

namespace SignCompat

theorem conjY_odd (e : Parker) (b : C) {ε : Cocode} (h : pair ΩC ε = 1) :
    conjY e ⟨0, b, ε⟩ = ⟨θ b e.code + e.sign,
      b + e.code + (θ e.code b + P (e.code : Fin 24 → ZMod 2) + pair e.code ε) • ΩC,
      Acocode e.code b + (thetaD e.code + ε)⟩ := by
  rw [conjY, conjD_of_odd e h]
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, SpinCoord.mul_δ, conjT, pair_zero_right, zero_add,
      pair_Acocode, Submodule.coe_add, Submodule.coe_smul, coe_ΩC, A_add_right, A_smul_Ω_right,
      A_self_mid e.code.2 b.2, add_zero]
  · simp only [SpinCoord.mul_a, conjT, zero_add]
    module
  · simp only [SpinCoord.mul_δ, conjT, zero_add]

end SignCompat
end CFSG.Monster.Visible
end
