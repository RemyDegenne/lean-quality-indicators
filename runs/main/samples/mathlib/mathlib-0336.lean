open scoped Finset

@[expose] public section

open scoped Pointwise

namespace Finset

variable {α β : Type*} [DecidableEq β]

scoped[Pointwise] attribute [instance] Finset.smulZeroClass Finset.distribSMul
  Finset.distribMulAction Finset.mulDistribMulAction

section GroupWithZero

variable [GroupWithZero α]

variable [DecidableEq α] {s : Finset α}

open scoped RightActions

@[simp] lemma inv_smul_finset_distrib₀ (a : α) (s : Finset α) : (a • s)⁻¹ = s⁻¹ <• a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext
    simp [← inv_smul_mem_iff₀, ha]

end GroupWithZero
end Finset
end
