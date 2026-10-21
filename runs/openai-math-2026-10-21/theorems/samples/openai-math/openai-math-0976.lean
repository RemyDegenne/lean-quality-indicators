namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace Percolation

universe u v

variable {V : Type u} {E : Type v}

section InvariantOperatorTrace

open scoped ComplexOrder InnerProduct

attribute [local instance] Classical.propDecidable

local instance spectralRealOperatorScalarTower :
    IsScalarTower ℝ (Hilbert V →L[ℂ] Hilbert V) (Hilbert V →L[ℂ] Hilbert V) where
  smul_assoc scalar first second := by
    ext vector vertex
    rfl

local instance spectralRealOperatorSMulCommClass :
    SMulCommClass ℝ (Hilbert V →L[ℂ] Hilbert V) (Hilbert V →L[ℂ] Hilbert V) where
  smul_comm scalar first second := by
    apply ContinuousLinearMap.ext
    intro vector
    exact (first.map_smul_of_tower scalar (second vector)).symm

local instance spectralNonUnitalContinuousFunctionalCalculus : NonUnitalContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)

local instance spectralContinuousFunctionalCalculus : ContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)

section RootTrace

variable {ι : Type*} [Fintype ι]

variable (root : ι → V) (weight : ι → ℝ)

theorem rootTrace_conjugate_le {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ) (hw : ∀ i, 0 ≤ weight i)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B)
    (hApos : 0 ≤ A) :
    rootTrace root weight (B*A*star B) ≤ ((‖B‖ ^ 2 : ℝ) : ℂ) * rootTrace root weight A := by
  calc
    rootTrace root weight (B*A*star B) = rootTrace root weight (star B*(B*A)) :=
      rootTrace_cyclic root weight htr (B*A) (star B) (hB.mul hA) hB.star
    _ = rootTrace root weight ((star B*B)*A) := by rw [mul_assoc]
    _ ≤ (‖star B*B‖ : ℂ) * rootTrace root weight A :=
      rootTrace_positive_mul_le root weight htr hw A (star B*B) hA (hB.star.mul hB)
        hApos (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg B))
    _ = ((‖B‖ ^ 2 : ℝ) : ℂ) * rootTrace root weight A := by
      have hnorm := CStarRing.norm_star_mul_self (x := B)
      have hn : ‖star B * B‖ = ‖B‖ ^ 2 := by
        convert hnorm using 1; simp only [pow_two]
      rw [hn]

 theorem matrixCoeff_gram (L M : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (L*star M) x y =
      inner ℂ (star L (lp.single 2 x (1:ℂ))) (star M (lp.single 2 y (1:ℂ))) := by
  rw [matrixCoeff_eq_inner]
  change inner ℂ _ (L ((ContinuousLinearMap.adjoint M) _)) = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rfl

 theorem matrixCoeff_gram_norm_sq_le
    (L M : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff (L*star M) x y‖ ^ 2 ≤
      (matrixCoeff (L*star L) x x).re * (matrixCoeff (M*star M) y y).re := by
  simp only [matrixCoeff_gram]
  have h := inner_mul_inner_self_le (𝕜 := ℂ)
      (star L (lp.single 2 x (1:ℂ))) (star M (lp.single 2 y (1:ℂ)))
  rw [norm_inner_symm (star M (lp.single 2 y (1:ℂ)))] at h
  simpa only [pow_two, RCLike.re_to_complex] using h

 theorem matrixCoeff_positive_product_norm_sq_le
    (A B : Hilbert V →L[ℂ] Hilbert V) (hA : 0 ≤ A) (x y : V) :
    ‖matrixCoeff (B*A) x y‖ ^ 2 ≤
      (matrixCoeff (B*A*star B) x x).re * (matrixCoeff A y y).re := by
  let S := CFC.sqrt A
  have hSS : S*S = A := CFC.sqrt_mul_sqrt_self A hA
  have hSstar : star S = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  convert matrixCoeff_gram_norm_sq_le (B*S) S x y using 1 <;>
    simp only [star_mul, hSstar, mul_assoc, ← mul_assoc S S, hSS]

end RootTrace
end InvariantOperatorTrace
end Percolation
end OAI
