public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v w w' u u'

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

@[reassoc (attr := simp)]
theorem biproductSumIso_hom_snd_π {J : Type w} {K : Type w'} (f : J → C) (g : K → C)
    [HasBiproduct f] [HasBiproduct g] [hs : HasBiproduct (Sum.elim f g)]
    [HasBinaryBiproduct (⨁ f) (⨁ g)] (k : K) :
    (biproductSumIso f g).hom ≫ biprod.snd ≫ biproduct.π g k =
      biproduct.π (Sum.elim f g) (Sum.inr k) := by
  rw [biproductSumIso_hom]
  dsimp +unfoldPartialApp only [Sum.elim] at hs ⊢
  simp

end TauCeti
end
