public section

namespace CFSG.Quasithin

namespace H

namespace Sp4

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix PairG

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose tau coe_tau lam
  coe_lam radical mem_unipotent_iff eq_sym2 tau_comm tau_injective lam_mul_tau_mul_inv
  unitri_mul_sym2_mul_transpose unitri)

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)

open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauSp_bijective)

open CFSG.RankThree.SubgroupLists (spForm spE spForm_spE_left spForm_mulVec spForm_apply
  exists_mem_statedSp_mulVec_eq)

open scoped Matrix

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)

local notation "ι₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)

local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)

local notation "ι₃" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

variable {K : Type} [Field K]

variable [CharP K 2] [Finite K]

omit [CharP K 2] in
theorem card_fixV_le_of_mem {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))}
    {a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)} (hab : pairAut a b ∈ A)
    (W₁ W₂ : Submodule K (Fin 2 ⊕ Fin 2 → K))
    (hW₁ : ∀ v ∈ fixV A, Multiplicative.toAdd (v : PairMod (Fin 2 ⊕ Fin 2) K).1 ∈ W₁)
    (hW₂ : ∀ v ∈ fixV A, Multiplicative.toAdd (v : PairMod (Fin 2 ⊕ Fin 2) K).2 ∈ W₂) :
    Nat.card ↥(fixV A) ≤ Nat.card {v : Fin 2 ⊕ Fin 2 → K // v ∈ W₁ ∧ toAddMap a v = v} *
      Nat.card {w : Fin 2 ⊕ Fin 2 → K // w ∈ W₂ ∧ toAddMap b w = w} := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun v =>
    (⟨Multiplicative.toAdd (v : PairMod (Fin 2 ⊕ Fin 2) K).1, hW₁ v v.2, ?_⟩,
      ⟨Multiplicative.toAdd (v : PairMod (Fin 2 ⊕ Fin 2) K).2, hW₂ v v.2, ?_⟩)) fun v w hvw => ?_
  · have := v.2 _ hab
    exact congrArg (fun p : PairMod (Fin 2 ⊕ Fin 2) K => Multiplicative.toAdd p.1) this
  · have := v.2 _ hab
    exact congrArg (fun p : PairMod (Fin 2 ⊕ Fin 2) K => Multiplicative.toAdd p.2) this
  · have h1 := congrArg (fun p => (p.1 : Fin 2 ⊕ Fin 2 → K)) hvw
    have h2 := congrArg (fun p => (p.2 : Fin 2 ⊕ Fin 2 → K)) hvw
    simp only at h1 h2
    exact Subtype.ext (Prod.ext (Multiplicative.toAdd.injective h1)
      (Multiplicative.toAdd.injective h2))

end Sp4
end H
end CFSG.Quasithin
end
