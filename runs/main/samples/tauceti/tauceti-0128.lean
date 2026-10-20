public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial IsLocalRing

universe u

namespace WeierstrassCurve

section CommRing

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section AffinePoint

variable {W} {x y : R} (h : W.toAffine.Equation x y)

theorem projModelAffinePoint_apply_eq_iff {x' y' : R} (h' : W.toAffine.Equation x' y')
    (s : Spec (.of R)) :
    W.projModelAffinePoint h s = W.projModelAffinePoint h' s ↔
      x - x' ∈ s.asIdeal ∧ y - y' ∈ s.asIdeal := by
  have := s.isPrime
  let g := algebraMap R s.asIdeal.ResidueField
  -- the closed point `t` of `Spec κ(s)` lies over `s`
  let t : Spec (.of s.asIdeal.ResidueField) := ⟨⊥, Ideal.isPrime_bot⟩
  have ht : Spec.map (CommRingCat.ofHom g) t = s := by
    refine PrimeSpectrum.ext ?_
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  -- two sections agree over `s` exactly when they agree as points with values in `κ(s)`
  conv_lhs => rw [← ht]
  rw [← TauCeti.AlgebraicGeometry.comp_eq_comp_iff_of_section
    (projModelAffinePoint_projModelOver h) (projModelAffinePoint_projModelOver h'),
    projModelAffinePoint_def, projModelAffinePoint_def,
    SpecMap_projModelPoint, SpecMap_projModelPoint,
    projModelPoint_eq_projModelPoint_iff_of_apply_eq (by simp)]
  simp only [true_and, ← Ideal.algebraMap_residueField_eq_zero, map_sub, sub_eq_zero]
  refine ⟨fun h ↦ ⟨congrFun h 0, congrFun h 1⟩, fun ⟨hx, hy⟩ ↦ funext fun k ↦ ?_⟩
  fin_cases k <;> simp [hx, hy, g]

end AffinePoint
end CommRing
end WeierstrassCurve
end
