public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) {x y : GridState n}

theorem maslovOℤ_sub_two_mul_card_OColumns {r : GridRectangleBetween x y} (hr : r.IsEmpty) :
    G.maslovOℤ y - 2 * ((G.OColumns r.toGridRectangle).card : ℤ) = G.maslovOℤ x - 1 := by
  have h := G.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one hr
  rw [G.maslovO_eq_intCast, G.maslovO_eq_intCast] at h
  exact_mod_cast h

end GridDiagram
end TauCeti
end
