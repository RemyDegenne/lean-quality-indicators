public section

namespace TauCeti

open Subgroup

variable {G : Type*} [Group G]

@[simp]
theorem _root_.Subgroup.IsComplement.coe_toRightFun_of_mem {H : Subgroup G} {R : Set G}
    (hR : IsComplement (H : Set G) R) {r : G} (hr : r ∈ R) : (hR.toRightFun r : G) = r := by
  have h := (isComplement_iff_existsUnique_mul_inv_mem.mp hR r).unique
    (hR.mul_inv_toRightFun_mem r) (y₂ := ⟨r, hr⟩) (by simp)
  exact congrArg Subtype.val h

end TauCeti
end
