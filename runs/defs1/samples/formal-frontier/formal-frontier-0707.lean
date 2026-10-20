public section

set_option warningAsError true

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace

namespace TopCat.Sheaf.CommRingForget

variable {X Y : TopCat.{v}} (g : X ⟶ Y)

/-- The natural transformation whose components are native adjunction mates. -/
@[expose] noncomputable def canonicalComparison :
    underlyingSheaf Y ⋙ TopCat.Sheaf.pullback (Type v) g ⟶
      TopCat.Sheaf.pullback CommRingCat.{v} g ⋙ underlyingSheaf X where
  app := canonicalComponent g
  naturality := by
    intro A B a
    exact canonicalComponent_naturality g a

end TopCat.Sheaf.CommRingForget
end
