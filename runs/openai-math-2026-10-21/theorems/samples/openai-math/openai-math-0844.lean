namespace OAI

section

noncomputable section

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal

open MeasureTheory Filter Set Module

universe u

open scoped TensorProduct

open Set Module

open MeasureTheory Set

open scoped ENNReal

open IsDiscreteValuationRing IsLocalRing

open scoped ENNReal BigOperators

open MeasureTheory Set IsDiscreteValuationRing

open Filter

open scoped BigOperators Topology

open NumberField

open scoped NumberField nonZeroDivisors

namespace PrimeDegreePackets

theorem exists_ideal_support_split {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (A : Ideal (𝓞 K)) : A ≠ ⊥ →
    ∃ I J : Ideal (𝓞 K), I ≠ ⊥ ∧ J ≠ ⊥ ∧ IdealSupportedAt S I ∧
      IdealCoprimeTo S J ∧ A = I * J := by
  classical
  induction A using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ A hA =>
    intro _
    have ha : A = 1 := by simpa only [Ideal.isUnit_iff, Ideal.one_eq_top] using hA
    refine ⟨1,1,one_ne_zero,one_ne_zero,idealSupportedAt_one S,idealCoprimeTo_one S hS,?_⟩
    simpa using ha
  | h₃ A P hA hP ih =>
    intro _
    obtain ⟨I,J,hI,hJ,hsI,hcJ,hIJ⟩ := ih hA
    let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    obtain ⟨p,e,_he,_hpP,hp,hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    by_cases hs : p ∈ S
    · refine ⟨P*I,J,mul_ne_zero hP.ne_zero hI,hJ,
        idealSupportedAt_mul (idealSupportedAt_of_norm_eq_prime_pow hp hs hnorm) hsI,hcJ,?_⟩
      rw [hIJ,mul_assoc]
    · refine ⟨I,P*J,hI,mul_ne_zero hP.ne_zero hJ,hsI,
        idealCoprimeTo_mul hS (idealCoprimeTo_of_norm_eq_prime_pow hS hp hs hnorm) hcJ,?_⟩
      rw [hIJ,mul_left_comm]

end PrimeDegreePackets
end
end
end OAI
