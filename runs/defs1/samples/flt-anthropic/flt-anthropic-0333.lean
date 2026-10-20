namespace P2MW.S_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank

set_option synthInstance.maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

attribute [-instance] Quotient.instLE_mathlib

section Fold_HerbrandQuotient

open Finset

namespace M4aLocalCFT

universe u

variable {A : Type u} [AddCommGroup A]

namespace HerbrandPair

variable (P : HerbrandPair A)

section Cyclic

variable (σ : AddAut A) (n : ℕ)

noncomputable def ofAddAut (hσ : σ ^ n = 1) : HerbrandPair A where
  derive := σ.toAddMonoidHom - AddMonoidHom.id A
  norm := ∑ i ∈ range n, (σ ^ i).toAddMonoidHom
  derive_norm a := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
      AddMonoidHom.finsetSum_apply, AddEquiv.coe_toAddMonoidHom]
    rw [map_sum, ← Finset.sum_sub_distrib]
    have hstep : ∀ i ∈ range n, σ ((σ ^ i) a) - (σ ^ i) a
        = (σ ^ (i + 1)) a - (σ ^ i) a := by
      intro i _
      rw [pow_succ', AddAut.mul_apply']
    rw [Finset.sum_congr rfl hstep, telescope σ n a, hσ]
    simp
  norm_derive a := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
      AddMonoidHom.finsetSum_apply, AddEquiv.coe_toAddMonoidHom]
    have hstep : ∀ i ∈ range n, (σ ^ i) (σ a - a) = (σ ^ (i + 1)) a - (σ ^ i) a := by
      intro i _
      rw [map_sub, pow_succ, AddAut.mul_apply']
    rw [Finset.sum_congr rfl hstep, telescope σ n a, hσ]
    simp

end Cyclic
end HerbrandPair
end M4aLocalCFT
end Fold_HerbrandQuotient
end P2MW.S_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank
