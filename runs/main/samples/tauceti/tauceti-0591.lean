public section

namespace TauCeti

open scoped commutatorElement

namespace IsProP

section Module

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (hG : IsProP p G) {N : Subgroup G} [N.Normal]
  [IsClosed (N : Set G)]

include hG

theorem ofMul_mk_demushkinWordTwoEven_of_le_three (a f : ℕ) {n : ℕ} (hn : n ≤ 3) {x : ℕ → G}
    (h0 : x 0 ∈ N) (h2 : x 2 ∈ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨_, demushkinWordTwoEven_mem a f n h0 (pow_mem h2 _)
        fun i hi ↦ absurd hi (by omega)⟩ : N) : TopologicalAbelianization N) =
      (1 + (a : completedGroupAlgebra ℤ_[p] (G ⧸ N)) +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (x 1 : G ⧸ N)⁻¹) •
          Additive.ofMul ((⟨x 0, h0⟩ : N) : TopologicalAbelianization N) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ N)) ^ f) •
          Additive.ofMul ((⟨x 2, h2⟩ : N) : TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  have hm : n / 2 - 1 = 0 := by omega
  have h : (⟨_, demushkinWordTwoEven_mem a f n h0 (pow_mem h2 _)
      fun i hi ↦ absurd hi (by omega)⟩ : N) =
      ⟨x 0 ^ (2 + a) * labuteComm (x 0) (x 1),
        mul_mem (pow_mem h0 _) (labuteComm_mem_of_mem_left h0 _)⟩ * (⟨x 2, h2⟩ : N) ^ 2 ^ f := by
    ext
    simp [demushkinWordTwoEven_def, hm, mul_assoc]
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_pow, ofMul_mul, ofMul_pow,
    hG.ofMul_mk_pow_mul_labuteComm h0 (x 1),
    ← Nat.cast_smul_eq_nsmul (completedGroupAlgebra ℤ_[p] (G ⧸ N))]
  congr 2 <;> norm_num [add_sub_right_comm]

end Module
end IsProP
end TauCeti
end
