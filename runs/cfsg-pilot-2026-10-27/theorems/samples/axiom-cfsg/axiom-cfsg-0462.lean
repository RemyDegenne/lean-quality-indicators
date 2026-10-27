public section

namespace CFSG.GH74.GLS.IVK.Prod3.LangF

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter

open scoped commutatorElement

section Basic

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

theorem mem_cen {K : Subgroup H} {a x : H} : x ∈ cen K a ↔ x ∈ K ∧ x * a = a * x := by
  rw [cen, mem_inf, mem_centralizer_singleton_iff]

end Basic
end CFSG.GH74.GLS.IVK.Prod3.LangF
end
