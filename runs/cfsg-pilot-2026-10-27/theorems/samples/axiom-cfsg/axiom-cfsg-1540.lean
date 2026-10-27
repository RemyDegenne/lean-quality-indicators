public section

namespace CFSG.RankThree.PartOne.KCUnitaryPlane

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]
  {B : V →ₛₗ[σ] V →ₗ[K] K} {P : Type*} [Group P] [Fintype P] {p : ℕ}
  (ρ : P →* LinearMap.GeneralLinearGroup K V)

section Geometry

theorem orth_line_line (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {L M : Subgroup P} (hL : Nat.card L = p) (hM : Nat.card M = p) (hne : L ≠ M) {u w : V}
    (hu : u ∈ lineSpace ρ B L) (hw : w ∈ lineSpace ρ B M) : B u w = 0 := by
  rw [← range_projLine ρ hP hpK hρ hB hBl hL] at hu
  rw [← range_projLine ρ hP hpK hρ hB hBl hM] at hw
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨w', rfl⟩ := hw
  rw [isSelfAdj_projLine ρ hρ L u' (projLine ρ M w')]
  have : projLine ρ L (projLine ρ M w') = 0 := by
    simpa using congrArg (fun f : Module.End K V => f w')
      (projLine_mul_projLine_of_ne ρ hP hpK hL hM hne)
  rw [this, map_zero]

end Geometry
end CFSG.RankThree.PartOne.KCUnitaryPlane
end
