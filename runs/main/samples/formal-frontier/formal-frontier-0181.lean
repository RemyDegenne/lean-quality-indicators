@[expose] public section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory

namespace Limits

theorem coproductDisjoint_iff_pairwise_inf_eq_bot {A : Type u} [Lattice A] [OrderBot A]
    {ι : Type v} [Finite ι] (X : ι → A) :
    CoproductDisjoint X ↔ ∀ i j : ι, i ≠ j → X i ⊓ X j = ⊥ := by
  constructor
  · intro h i j hij
    have : CoproductDisjoint X := h
    have hinitial : IsInitial (X i ⊓ X j) :=
      IsInitial.ofCoproductDisjointOfIsColimitOfIsLimit hij
        (coproductIsCoproduct X) (isPullback_inf (Sigma.ι X i) (Sigma.ι X j)).isLimit
    exact le_antisymm (hinitial.to ⊥).le bot_le
  · intro h
    refine { nonempty_isInitial_of_ne := ?_, mono_inj := ?_ }
    · intro c hc i j hij s hs
      have hpoint : s.pt = X i ⊓ X j :=
        (hs.conePointUniqueUpToIso (isPullback_inf (c.inj i) (c.inj j)).isLimit).to_eq
      rw [hpoint, h i j hij]
      exact ⟨Preorder.isInitialBot A⟩
    · intro c hc i
      exact ⟨fun _ _ _ => Subsingleton.elim _ _⟩

end Limits
end CategoryTheory
end
