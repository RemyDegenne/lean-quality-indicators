namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

namespace Sparse.GraphGeometry

open FinProbability

variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]

theorem meetingTops_card_le (hΓ : Γ.Connected) (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) {n : ℕ} (hn : 0<n)
    (tops : Set (Finset Y))
    (htop : ∀ σ∈tops, σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) (s : ℝ) (hs : 0 ≤ s) :
    Nat.card (MeetingTops Γ hΓ n tops c s) ≤
      c.coeff.support.card * D^(⌊s * Real.sqrt (n : ℝ)⌋₊+1) * D^(2*n) := by
  let B := c.coeff.support.biUnion (neighborhood Γ ⌊s * Real.sqrt (n : ℝ)⌋₊)
  let f : MeetingTops Γ hΓ n tops c s → GraphCounting.ConnectedThrough Γ B n := fun σ =>
    ⟨σ.val,(htop σ.val σ.property.1).1,(htop σ.val σ.property.1).2,by
      obtain ⟨p,hp,hball⟩ := σ.property.2
      exact meeting_simplex_contact Γ hΓ hn c p σ.val hp s hs hball⟩
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    exact congrArg (fun x : GraphCounting.ConnectedThrough Γ B n => x.val) h
  have : Finite (GraphCounting.ConnectedThrough Γ B n) :=
    GraphCounting.connectedThrough_finite Γ B n
  calc
    _ ≤ Nat.card (GraphCounting.ConnectedThrough Γ B n) := Nat.card_le_card_of_injective f hf
    _ ≤ B.card * D^(2*n) := GraphCounting.connectedThrough_card_le Γ D hdeg B n
    _ ≤ _ := Nat.mul_le_mul_right _ (supportNeighborhood_card_le Γ D hD hdeg _ _)

end Sparse.GraphGeometry
end BassTrace
end
end OAI
