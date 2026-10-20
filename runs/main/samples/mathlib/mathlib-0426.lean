@[expose] public section

open Order Set

variable {ι : Type*} [Preorder ι] {F₁ F₂ F X : ι → Type*}

section DirectedSystem

variable {T₁ : ∀ ⦃i j : ι⦄, i ≤ j → Sort*} (f₁ : ∀ i j (h : i ≤ j), T₁ h)

variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T₁ h) (F₁ i) (F₁ j)] [DirectedSystem F₁ (f₁ · · ·)]

variable {T₂ : ∀ ⦃i j : ι⦄, i ≤ j → Sort*} (f₂ : ∀ i j (h : i ≤ j), T₂ h)

variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T₂ h) (F₂ i) (F₂ j)] [DirectedSystem F₂ (f₂ · · ·)]

variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort*} (f : ∀ i j (h : i ≤ j), T h)

variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (F i) (F j)] [DirectedSystem F (f · · ·)]

namespace DirectLimit

open DirectedSystem

variable [IsDirectedOrder ι]

section lift₂

variable {C : Sort*} (ih : ∀ i, F₁ i → F₂ i → C)
  (compat : ∀ i j h x y, ih i x y = ih j (f₁ i j h x) (f₂ i j h y))

theorem lift₂_def₂ (x : Σ i, F₁ i) (y : Σ i, F₂ i) (i) (hxi : x.1 ≤ i) (hyi : y.1 ≤ i) :
    DirectLimit.lift₂ f₁ f₂ ih compat ⟦x⟧ ⟦y⟧ = ih i (f₁ _ _ hxi x.2) (f₂ _ _ hyi y.2) :=
  (lift₂Aux _ _ _ compat _ _).2 ..

end lift₂
end DirectLimit
end DirectedSystem
end
