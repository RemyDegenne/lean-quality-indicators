public section

universe u

open CategoryTheory Category Preadditive Module

namespace TauCeti

variable (S : Type u) [CommRing S] (w : S)

namespace CurvedDuplex

variable {S w}

/-- The dual of a morphism of curved duplexes is a morphism from the dual of the target to the
dual of the source, with transposed components. The two commutativity conditions of `f` enter
with the two differentials exchanged, which is what the crossed transposes need. -/
def dualMap {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] (f : X ⟶ Y) :
    Y.dual ⟶ X.dual :=
  homMk (FGModuleCat.dualMap f.f₀) (FGModuleCat.dualMap f.f₁)
    (by rw [← FGModuleCat.dualMap_comp, ← FGModuleCat.dualMap_comp, f.comm₁])
    (by
      simp only [comp_neg, neg_comp]
      rw [← FGModuleCat.dualMap_comp, ← FGModuleCat.dualMap_comp, f.comm₀])

end CurvedDuplex
end TauCeti
end
