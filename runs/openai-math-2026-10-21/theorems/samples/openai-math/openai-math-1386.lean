namespace OAI

namespace Balanced.Local

theorem allTokensDistinct_eligible {F : Type*} {b κ : ℕ}
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (ha : AllTokensDistinct a) : Eligible P a := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    have h' : Sum.inl i = (Sum.inl j : DirectionToken b κ) := ha h
    exact Sum.inl.inj h'
  · intro i j h
    have h' : Sum.inr i = (Sum.inr j : DirectionToken b κ) := ha h
    exact Sum.inr.inj h'
  · intro i j h
    have h' : Sum.inr (P.classOf i j) = (Sum.inl i : DirectionToken b κ) := ha h
    cases h'

end Balanced.Local
end OAI
