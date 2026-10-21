namespace OAI

section

namespace ElementaryPositivity.ShufflePolynomiality

open MvPolynomial

variable {α : Type*} [DecidableEq α]

section Packs

variable {I : Type*} [Fintype I] [DecidableEq I]

variable (V : I → Type*) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

lemma pack_alternate_diagonal (E : I → Prop) [DecidablePred E]
    (f : MvPolynomial (Σ i,V i) ℚ) (i : I) (a b : V i)
    (hi : E i) (hab : a ≠ b) :
    diagonal ⟨i,a⟩ ⟨i,b⟩ ∣ alternate (packAction V) (packSign V E) f := by
  apply diagonal_dvd_alternate (packAction V) (packSign V E) f
    ⟨i,a⟩ ⟨i,b⟩ (Function.update 1 i (Equiv.swap a b))
  · exact packAction_transposition V i a b
  · exact packSign_transposition V E i a b hi hab

end Packs
end ElementaryPositivity.ShufflePolynomiality
end
end OAI
