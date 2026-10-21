namespace OAI

namespace KervaireRibbon

section

open Monoid Multiplicative

variable {A : Type*} [Group A]

lemma unit_syllables_every (w : FreeProd A) :
    ∃ l : List (ℤ × A), 2 ≤ l.length ∧ UnitSyllables l ∧ syllableEval l = w := by
  obtain ⟨g,l,hl,rfl⟩ := normalized_every w
  refine ⟨(1,1)::(-1,g)::l,by simp,?_,?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl rfl
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr rfl
      · exact hl x hx
  · simp only [syllableEval,List.map_cons,List.prod_cons,map_one,mul_one,
      ofAdd_neg,map_inv]
    group

end
end KervaireRibbon
end OAI
