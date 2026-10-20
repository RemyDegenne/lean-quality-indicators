public section

open Set

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

theorem swirl_hG_of_meridionalSmallness {ρ Rstar η : ℝ} {u : ParabolicPoint → Vec3}
    (hsmall : MeridionalSmallness ρ u) (hη : 0 < η) (hRstar : Rstar ≤ ρ) :
    ∃ tη ∈ Ioo (-1 : ℝ) 0, ∀ t ∈ Ioo tη (0 : ℝ), ∀ x₁ x₃ : ℝ,
      meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t) := by
  rcases tendsto_radialQuotient_of_meridionalSmallness hsmall η hη with ⟨tη, htη, hbound⟩
  refine ⟨tη, htη, ?_⟩
  intro t ht x₁ x₃ hmem
  have hmem' : meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ :=
    vec3Ball_mono hRstar hmem
  have h := hbound t ht x₁ x₃ hmem'
  have hpos : 0 < -t := by
    have : t < 0 := ht.2
    linarith only [this]
  rw [le_div_iff₀ hpos]
  calc
    |radialQuotient u (meridional x₁ x₃, t)| * (-t) = (-t) * |radialQuotient u (meridional x₁
      x₃, t)| := by
      ring
    _ ≤ η := h

end CIV
end
end
