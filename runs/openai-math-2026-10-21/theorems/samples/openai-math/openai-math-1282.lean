namespace OAI

section

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C D : StrictOmegaCategory.{0}} {n k : ℕ}

theorem evaluation_matching (p : PastingGlobe.category n n k ⟶ C)
    (u : model.obj C ⟶ D) :
    model.map (Globe.faceMap true k n) ≫ (model.map (PastingGlobe.left n n k ≫ p) ≫ u) =
      model.map (Globe.faceMap false k n) ≫ (model.map (PastingGlobe.right n n k ≫ p) ≫ u) := by
  simp only [← Category.assoc, ← model.map_comp]
  exact congrArg (fun q => model.map (q ≫ p) ≫ u)
    (pushout.condition (f := Globe.faceMap true k n) (g := Globe.faceMap false k n))

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping
end
end OAI
