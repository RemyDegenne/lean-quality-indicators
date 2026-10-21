namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits

open scoped ENNReal ZeroObject

open CategoryTheory

attribute [local instance] Classical.propDecidable

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian

namespace Lech.ImageCech

open SetLike Graded

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)
  {h : ℕ} (y : Fin h → A) (hy : ∀ i, y i ∈ G 1)

omit [GradedAlgebra G] [GradedAlgebra H] in
lemma image_denominator (s : Finset (Fin h)) :
    g (GradedChart.denominator y s) = GradedChart.denominator (fun i => g (y i)) s := by
  simp only [GradedChart.denominator,map_prod]

end Lech.ImageCech
end
end OAI
