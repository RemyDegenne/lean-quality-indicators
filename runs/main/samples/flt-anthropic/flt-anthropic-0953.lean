namespace P2MW.S_CuspidalType_eq_or_eq_pow_of_isConj_torus

set_option autoImplicit false

open Polynomial CuspidalType

set_option maxHeartbeats 1600000

namespace Ws23NV3

open Polynomial CuspidalType

variable (q : ℕ) [Fact q.Prime]

theorem main_b {α α' : (GaloisField q 2)ˣ} (h : IsConj (torus q α) (torus q α')) :
    α' = α ∨ α' = α ^ q := by
  classical
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  set p : (ZMod q)[X] := ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly with hp
  have hp' : ((torus q α' : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly = p := by
    rw [← hc, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

  have hα : aeval (α : GaloisField q 2) p = 0 := aeval_charpoly_torus q α
  have hα' : aeval (α' : GaloisField q 2) p = 0 := by rw [← hp']; exact aeval_charpoly_torus q α'
  have hαq : aeval ((α : GaloisField q 2) ^ q) p = 0 := by
    rw [← frob_apply, aeval_algHom_apply, hα, map_zero]
  have hmonic : p.Monic := Matrix.charpoly_monic _
  have hdeg : p.natDegree = 2 := by rw [hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

  set P : (GaloisField q 2)[X] := p.map (algebraMap (ZMod q) (GaloisField q 2)) with hP
  have evP : ∀ y : GaloisField q 2, eval y P = aeval y p := fun y => by rw [hP, eval_map, aeval_def]
  have hPm : P.Monic := hmonic.map _
  have hPdeg : P.natDegree = 2 := by rw [hP, hmonic.natDegree_map, hdeg]
  by_cases hfix : (α : GaloisField q 2) ^ q = α
  ·
    obtain ⟨a, ha⟩ := mem_range_algebraMap_of_pow_eq q hfix
    have hpa : p = (X - C a) ^ 2 := by
      rw [hp, coe_torus, ← ha, lmul_algebraMap, LinearMap.toMatrix_algebraMap, Matrix.scalar_apply,
        Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    left
    apply Units.ext
    have h2 : aeval (α' : GaloisField q 2) ((X - C a) ^ 2) = 0 := by rw [← hpa]; exact hα'
    rw [map_pow, map_sub, aeval_X, aeval_C] at h2
    have h3 := sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
    rw [h3, ha]
  ·
    have hne : (α : GaloisField q 2) ^ q ≠ α := hfix
    have hQm : ((X - C (α : GaloisField q 2)) * (X - C ((α : GaloisField q 2) ^ q))).Monic :=
      (monic_X_sub_C _).mul (monic_X_sub_C _)
    have hQdeg : ((X - C (α : GaloisField q 2)) * (X - C ((α : GaloisField q 2) ^ q))).natDegree = 2 := by
      rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), natDegree_X_sub_C, natDegree_X_sub_C]
    have hPQ : P = (X - C (α : GaloisField q 2)) * (X - C ((α : GaloisField q 2) ^ q)) := by
      by_contra hneq
      have hD0 : P - (X - C (α : GaloisField q 2)) * (X - C ((α : GaloisField q 2) ^ q)) ≠ 0 := sub_ne_zero.mpr hneq
      have hdegPQ : P.degree = ((X - C (α : GaloisField q 2)) * (X - C ((α : GaloisField q 2) ^ q))).degree := by
        rw [degree_eq_natDegree hPm.ne_zero, degree_eq_natDegree hQm.ne_zero, hPdeg, hQdeg]
      have hlcPQ : P.leadingCoeff = ((X - C (α : GaloisField q 2)) * (X - C ((α : GaloisField q 2) ^ q))).leadingCoeff := by
        rw [hPm.leadingCoeff, hQm.leadingCoeff]
      have hdeglt := Polynomial.degree_sub_lt hdegPQ hPm.ne_zero hlcPQ
      have hDnat : (P - (X - C (α : GaloisField q 2)) * (X - C ((α : GaloisField q 2) ^ q))).natDegree < 2 := by
        rw [Polynomial.natDegree_lt_iff_degree_lt hD0]
        refine lt_of_lt_of_eq hdeglt ?_
        rw [degree_eq_natDegree hPm.ne_zero, hPdeg]
      have hs : ({(α : GaloisField q 2), (α : GaloisField q 2) ^ q} : Finset (GaloisField q 2)).card = 2 :=
        Finset.card_pair (Ne.symm hne)
      refine hD0 (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
        ({(α : GaloisField q 2), (α : GaloisField q 2) ^ q} : Finset (GaloisField q 2)) (fun y hy => ?_)
        (by rw [hs]; exact hDnat))
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · rw [eval_sub, evP, hα, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, sub_zero]
      · rw [eval_sub, evP, hαq, eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C, sub_self, mul_zero, sub_zero]
    have h4 : eval (α' : GaloisField q 2) P = 0 := by rw [evP]; exact hα'
    rw [hPQ, eval_mul, mul_eq_zero, eval_sub, eval_X, eval_C, eval_sub, eval_X, eval_C] at h4
    rcases h4 with h4 | h4
    · left; exact Units.ext (sub_eq_zero.mp h4)
    · right; apply Units.ext; rw [Units.val_pow_eq_pow_val]; exact sub_eq_zero.mp h4

end Ws23NV3
end P2MW.S_CuspidalType_eq_or_eq_pow_of_isConj_torus
