namespace P2MW.S_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP

set_option maxHeartbeats 3200000

set_option synthInstance.maxHeartbeats 1600000

open Polynomial

namespace S12R4

theorem exists_isPrimitive_aeval_eq_zero (A : ValuationSubring (AlgebraicClosure ℚ)) (a : A) :
    ∃ Q : ℤ[X], Q.IsPrimitive ∧ aeval a Q = 0 := by
  have halg : IsAlgebraic ℤ (a : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic (a : AlgebraicClosure ℚ))
  obtain ⟨P, hP0, hP⟩ := halg
  refine ⟨P.primPart, P.isPrimitive_primPart, ?_⟩
  have hc : (P.content : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast (mt content_eq_zero_iff.mp hP0)
  have hprim : aeval (a : AlgebraicClosure ℚ) P.primPart = 0 := by
    rw [P.eq_C_content_mul_primPart, map_mul, aeval_C] at hP
    simpa [hc] using hP

  apply Subtype.val_injective
  let f : A →ₐ[ℤ] AlgebraicClosure ℚ := (A.toSubring.subtype).toIntAlgHom
  have hf : ∀ x : A, f x = (x : AlgebraicClosure ℚ) := fun x => rfl
  show (aeval a P.primPart : A).val = (0 : A).val
  rw [← hf, ← hf, ← Polynomial.aeval_algHom_apply, hf, hprim]
  rfl

end S12R4
end P2MW.S_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
