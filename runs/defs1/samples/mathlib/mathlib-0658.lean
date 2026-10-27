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

section map

variable (ih : ∀ i, F₁ i → F₂ i) (compat : ∀ i j h x, f₂ i j h (ih i x) = ih j (f₁ i j h x))

/-- To define a function from the direct limit, it suffices to provide one function from each
component subject to a compatibility condition. -/
def map (z : DirectLimit F₁ f₁) : DirectLimit F₂ f₂ :=
  z.lift _ (fun i x ↦ ⟦⟨i, ih i x⟩⟧) fun j k h x ↦ Quotient.sound <|
    have ⟨i, hji, hki⟩ := exists_ge_ge j k
    ⟨i, hji, hki, by simp_rw [compat, map_map']⟩

end map
end DirectLimit
end DirectedSystem
end
