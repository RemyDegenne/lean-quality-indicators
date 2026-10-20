@[expose] public section

open scoped Topology

namespace PadicInt

theorem int_span_three_two_proper_dense :
    Submodule.span ℤ {(3 : ℤ_[2])} ≠ ⊤ ∧
      Dense (Submodule.span ℤ {(3 : ℤ_[2])} : Set ℤ_[2]) := by
  constructor
  · simpa only [Int.cast_ofNat] using int_span_intCast_ne_top 2 3
  · simpa only [Int.cast_ofNat] using
      dense_int_span_intCast (p := 2) 3 (by decide : ¬ (2 : ℤ) ∣ 3)

end PadicInt
end
