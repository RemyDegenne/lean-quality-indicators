universe u v w

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {H : Type v} {K : Type w}
  [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
  [LinearOrder H] [AddCommGroup H] [IsOrderedAddMonoid H]
  [CommRing K]

@[simp]
theorem coe_mapDomain (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g')
    (b : Nonpositive G K) :
    (mapDomain f hfi hf b : K⟦H⟧) =
      HahnSeries.embDomain (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (b : K⟦G⟧) :=
  (rfl)

end HahnSeries.Nonpositive
end
