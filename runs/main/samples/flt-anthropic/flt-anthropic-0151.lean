namespace P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

scoped instance instCharZeroAdicCompletionRingOfIntegers_s18 {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CharZero (v.adicCompletion K) :=
  ((algebraMap K (v.adicCompletion K)).charZero_iff (algebraMap K (v.adicCompletion K)).injective).mp inferInstance

scoped instance fact_prime_two_s18 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

scoped instance fact_prime_three_s18 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

scoped instance fact_prime_seven_s18 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

section

section

p2m_open

open ModularCurve

namespace FLT

namespace NumberTheory

open TotallyDefiniteQuaternionAlgebra FreyPackage

p2m_open_scoped

section SplitEngine

p2m_open

variable {F : Type*} [Field F] [CharZero F]

theorem kw_hjoint_normBasis_liftHom_apply {a b : F} {u v : F}
    (huv : b = u * u - a * (v * v)) (z : QuaternionAlgebra F a 0 b) :
    (kw_hjoint_normBasis huv).liftHom z =
      !![z.re + u * z.imJ + a * v * z.imK, a * z.imI - a * v * z.imJ - a * u * z.imK;
         z.imI + v * z.imJ + u * z.imK, z.re - u * z.imJ - a * v * z.imK] := by
  have h : (kw_hjoint_normBasis huv).liftHom z
      = algebraMap F (Matrix (Fin 2) (Fin 2) F) z.re
        + z.imI • !![(0:F), a; 1, 0] + z.imJ • !![u, -(a*v); v, -u]
        + z.imK • !![a*v, -(a*u); u, -(a*v)] := rfl
  rw [h]
  ext r s; fin_cases r <;> fin_cases s <;>
    simp [Matrix.algebraMap_matrix_apply] <;> ring

end SplitEngine
end NumberTheory
end FLT
end
end
end P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
