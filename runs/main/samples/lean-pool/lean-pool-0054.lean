open Cardinal

universe u v w

public noncomputable section

namespace HahnSeries

variable {G : Type u} {H : Type u} {R : Type v} {κ : Cardinal.{u}}

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

variable [AddCommGroup H] [LinearOrder H] [IsOrderedAddMonoid H]

variable [Field R] [Fact (aleph0 < κ)]

@[simp]
theorem CardSuppLTTruncationIntegerPart.coe_mapDomain
    (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    (((CardSuppLTTruncationIntegerPart.mapDomain f hfi hf Z x :
      cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z) :
        CardSuppLTField (G := H) (R := R) (κ := κ)) : R⟦H⟧) =
      HahnSeries.embDomain (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (x : R⟦G⟧) :=
  (rfl)

end HahnSeries
end
