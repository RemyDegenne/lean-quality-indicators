public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {A : Type*} [Group A]

variable {E} {φ : A →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}

section NaiveLocus

variable {H : Over S} (u : A →* (H ⟶ Over.mk E.structureMap))

theorem isClopen_naiveLocus [Finite A] {N : ℕ} (hN : ∀ s : S, (N : S.residueField s) ≠ 0)
    (hu : ∀ a, u a ^ N = 1) : IsClopen (naiveLocus u) := by
  have h : naiveLocus u = ⋂ (a : A) (_ : a ≠ 1), (Set.range (equalizer.ι (u a) 1).left)ᶜ := by
    ext h
    simp [range_equalizer_ι_left_one]
  rw [h]
  refine isClopen_iInter_of_finite fun a ↦ isClopen_iInter_of_finite fun _ ↦
    (E.isClopen_range_equalizer_ι_left_of_mulBy_eq_one (n := N) (fun s ↦ ?_) ?_ (by simp)).compl
  · exact_mod_cast hN s
  · rw [comp_mulBy, zpow_natCast, hu a]

end NaiveLocus
end TauCeti.AlgebraicGeometry.EllipticCurveGeom
end
