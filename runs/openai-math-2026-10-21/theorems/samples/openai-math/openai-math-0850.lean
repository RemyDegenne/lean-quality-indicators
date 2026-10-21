namespace OAI

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem exists_bounded_terminal_chain (B : Finset G) (Admissible : Finset G → Prop)
    {K kappa : ℝ} (hK : 0 < K) (hkappa : 0 < kappa) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ B → f x = 0) :
    ∃ g cs, Chain B Admissible K kappa f g cs ∧
      cs.length ≤ (positiveSupport f).card ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ f x) ∧ (∀ x, x ∉ B → g x = 0) ∧
      ((𝔼 x ∈ B, g x) < kappa ∨ ∀ C, Admissible C → (𝔼 x ∈ C, g x) ≤ K * (𝔼 x ∈ B, g x)) := by
  obtain ⟨g, cs, hchain, hterminal⟩ := exists_terminal_chain B Admissible hK hkappa f
  exact ⟨g, cs, hchain, hchain.length_le_support hK hkappa, hchain.bounds hf,
    hchain.supported hf hsupport, hterminal⟩

end Erdos3.Peeling
end OAI
