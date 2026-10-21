namespace OAI

universe uι

noncomputable section

open Set MeasureTheory Metric Filter Topology

open scoped ENNReal RealInnerProductSpace Pointwise

namespace PettyProjection.Spherical

local instance (n : ℕ) : CompleteSpace (Space n →L[ℝ] Space n) :=
  FiniteDimensional.complete ℝ _

local instance (n : ℕ) : NormedAlgebra ℚ (Space n →L[ℝ] Space n) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

open MvPolynomial

lemma energy_harmonic_right {n d : ℕ} [NeZero n] {f : Space n → ℝ}
    {p : MvPolynomial (Fin n) ℝ} (hf : ContDiff ℝ 1 f) (hp : p.IsHomogeneous d)
    (hΔp : laplacePolynomial p = 0) :
    energy f (polynomialFunction p) = eigenvalue n d *
      mean (fun u : Sphere n => f u * polynomialFunction p u) := by
  have h := mean_casimir hf ((polynomialFunction_contDiff p).of_le le_top)
  simp_rw [casimir_harmonic hp hΔp, mul_left_comm (f _) (-eigenvalue n d)] at h
  rw [mean, integral_const_mul] at h
  unfold mean
  linarith

end PettyProjection.Spherical
end
end OAI
