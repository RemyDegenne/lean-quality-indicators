@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

section

open scoped BigOperators

namespace HigherYoungIsotropicCoordinateHomogeneity

open MetricCodes.Spherical.HigherHarmonicYoung

open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors

open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence

theorem inverseIsotropicCoordinateGenerator_isHomogeneous
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (v : Fin ((r + 1) * n)) :
    (inverseIsotropicCoordinateGenerator h v).IsHomogeneous 1 := by
  have hsmul (c : ℂ)
      (p : MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (hp : p.IsHomogeneous 1) : (c • p).IsHomogeneous 1 := by
    rw [MvPolynomial.smul_eq_C_mul]
    exact hp.C_mul c
  unfold inverseIsotropicCoordinateGenerator
  dsimp only
  split_ifs
  · exact hsmul _ _
      ((MvPolynomial.isHomogeneous_X _ _).add
        (MvPolynomial.isHomogeneous_X _ _))
  · exact (hsmul _ _ (MvPolynomial.isHomogeneous_X _ _)).add
      (hsmul _ _ (MvPolynomial.isHomogeneous_X _ _))
  · exact MvPolynomial.isHomogeneous_X _ _

end HigherYoungIsotropicCoordinateHomogeneity
end
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
