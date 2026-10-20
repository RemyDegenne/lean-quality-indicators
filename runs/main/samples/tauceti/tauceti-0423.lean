public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

section Group

variable (G : Type u) [Group G]

variable {G}

variable (G)

variable {G}

theorem autCompForgetActionMulEquiv_inv_app_apply {C : Type*} [Category C]
    (e : C ⥤ Action (Type u) G) [e.IsEquivalence] (g : G) (p : C) (x : ToType (e.obj p)) :
    (autCompForgetActionMulEquiv G e g).asIso.inv.app p x = g⁻¹ • x := by
  rw [autCompForgetActionMulEquiv_apply, unitsAutCompForgetActionMulEquiv_inv_app_apply,
    ← map_inv, val_toUnits_apply]

end Group
end TauCeti
end
end
