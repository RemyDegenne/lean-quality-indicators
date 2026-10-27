public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Sporadic.Schreier.Co3.Native CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates Matrix

theorem Co3_faithful_permutation_action :
    (∀ r < 276, ∀ r' < 276, co3Form r = co3Form r' → r = r') ∧
    (∀ r < 276, ∃ φ : Module.Dual (ZMod 2) Co3V, ∀ v, φ v = co3Form r v - co3Form 0 v) ∧
    (∃ b : Module.Basis (Fin 22) (ZMod 2) (Module.Dual (ZMod 2) Co3V), ∀ (k : Fin 22) v,
      b k v = co3Form (co3DiffIdx.getD k 0) v - co3Form 0 v) ∧
    (∀ (r : Fin 276) (v : Co3V), co3Form r (co3A1⁻¹ *ᵥ v) = co3Form (co3GenPerm 0 r) v) ∧
    (∀ (r : Fin 276) (v : Co3V), co3Form r (co3A2⁻¹ *ᵥ v) = co3Form (co3GenPerm 1 r) v) ∧
    (∀ (u : Blueprint.NativeSporadic.Co3) (r : Fin 276) (v : Co3V),
      co3Form ((co3PermEquiv u : Equiv.Perm (Fin 276)) r) v =
        co3Form r ((u⁻¹ : Blueprint.NativeSporadic.Co3).val.val *ᵥ v)) ∧
    co3SeedA.val.val = co3A1 ∧ co3SeedB.val.val = co3A2 ∧
    (co3PermEquiv co3SeedA : Equiv.Perm (Fin 276)) = co3GenPerm 0 ∧
    (co3PermEquiv co3SeedB : Equiv.Perm (Fin 276)) = co3GenPerm 1 := by
  have hA : (((co3SeedGL 0)⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      co3A1⁻¹ := by
    rw [Matrix.coe_units_inv, co3SeedGL_val, ite_eq_left rfl]
  have hB : (((co3SeedGL 1)⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      co3A2⁻¹ := by
    rw [Matrix.coe_units_inv, co3SeedGL_val, ite_eq_right one_ne_zero]
  refine ⟨fun r hr r' hr' h => co3Form_injective hr hr' h,
    fun r hr => ⟨co3DiffFun r, co3Form_sub hr⟩, ⟨co3DiffBasis, fun k v => co3DiffBasis_apply k v⟩,
    fun r v => ?_, fun r v => ?_, co3Form_permEquiv, co3SeedA_val, co3SeedB_val,
    co3PermEquiv_seedA, co3PermEquiv_seedB⟩
  · rw [← hA]
    exact co3Form_seed_inv (by norm_num) r v
  · rw [← hB]
    exact co3Form_seed_inv (by norm_num) r v

end CFSG.Sporadic.Schreier.Co3
end
