public noncomputable section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module Matrix

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary

open CFSG.GH74.GLS.IVK

section Basis

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

section Adapted

variable {A W : Submodule E V} (Q : AdaptedONB B A W) (hc : IsCompl A W)

theorem AdaptedONB.signU_A_mem (hG : ∀ α β, B (Q.b hc α) (Q.b hc β) = if α = β then 1 else 0)
    (S₀ : Finset (Fin (finrank E A))) (hS : Even S₀.card) :
    signU (Q.b hc) hG (S₀.map Function.Embedding.inl) ∈ summandUnitarySet B A W := by
  refine ⟨fun w hw => Q.signOp_fix_W hc (fun j => by simp) hw,
    fun a ha => Q.signOp_mem_A hc _ ha, ?_⟩
  show LinearMap.det ((signOp (Q.b hc) (S₀.map Function.Embedding.inl)).restrict _) = 1
  rw [Q.det_restrict_signOp hc, hS.neg_one_pow]

end Adapted
end Basis
end CFSG.GH74.GLS.IVK.Proofs2
end
