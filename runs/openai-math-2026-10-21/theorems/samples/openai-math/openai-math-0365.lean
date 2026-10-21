namespace OAI

namespace LittleFinitistic.RectificationAcyclic

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

variable {C : Type*} [Category C] [Abelian C]

theorem inclusion_homotopy_inverse (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (hQ : S.X₃.Acyclic) (hi : ℤ)
    [S.X₁.IsStrictlyLE hi] [S.X₂.IsStrictlyLE hi]
    [∀ i, Projective (S.X₁.X i)] [∀ i, Projective (S.X₂.X i)] :
    ∃ g : S.X₂ ⟶ S.X₁, Nonempty (Homotopy (S.f ≫ g) (𝟙 S.X₁)) ∧
      Nonempty (Homotopy (g ≫ S.f) (𝟙 S.X₂)) := by
  let := quasiIso_of_acyclic_quotient S hS hQ
  exact bounded_projective_homotopy_inverse S.f hi

end LittleFinitistic.RectificationAcyclic
end OAI
