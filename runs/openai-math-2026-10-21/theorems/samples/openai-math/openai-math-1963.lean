namespace OAI

section

section

section

noncomputable section

section

section

namespace CannonPairs

open Finset

attribute [local instance] Classical.propDecidable

lemma card_filter_product {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (rel : ι → κ → Prop) :
    ((S ×ˢ T).filter (fun p => rel p.1 p.2)).card =
      ∑ i ∈ S, (T.filter (rel i)).card := by
  classical
  simp only [card_eq_sum_ones,sum_filter,sum_product]

end CannonPairs
end
end
end
end
end
end
end OAI
