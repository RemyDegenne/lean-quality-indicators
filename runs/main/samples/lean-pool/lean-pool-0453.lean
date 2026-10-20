@[expose] public section

noncomputable section

open scoped BigOperators

open MvPolynomial

namespace KoetheMultiProjective

variable {k : Type*} {N : ℕ}

theorem Balanced.add_iff_right {d e : Vars N →₀ ℕ} (hd : Balanced d) :
    Balanced (d + e) ↔ Balanced e := by
  constructor
  · intro h b c
    have := h b c
    simpa only [blockDegree_add, hd b c, Nat.add_left_cancel_iff] using this
  · exact hd.add

end KoetheMultiProjective
end
end
