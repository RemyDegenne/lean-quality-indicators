namespace OAI

noncomputable section

namespace Ostmann.Arithmetic

open Ostmann.Construction

open scoped FourierTransform SchwartzMap

theorem positive_initial_product {b s k : ℕ} (x : InitialCoordinates b s k) (hx : x.Positive) :
    0 < x.product := by
  rcases hx with ⟨hg, hb, hs, ht, hc⟩
  unfold InitialCoordinates.product
  exact mul_pos (mul_pos (mul_pos (mul_pos
    (Finset.prod_pos (fun h _ => hg h))
    (Finset.prod_pos (fun h _ => Finset.prod_pos (fun i _ => hb h i))))
    (Finset.prod_pos (fun h _ => Finset.prod_pos (fun i _ => hs h i))))
    (Finset.prod_pos (fun h _ => Finset.prod_pos (fun i _ => ht h i))))
    (Finset.prod_pos (fun h _ => Finset.prod_pos (fun j _ => Finset.prod_pos (fun i _ => hc h j i))))

end Ostmann.Arithmetic
end
end OAI
