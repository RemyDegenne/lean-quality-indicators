@[expose] public section

namespace BeyondBethe

open Complexity

theorem rawRatListSupportProduct_value (acc : RawRat) : ∀ xs : List ℚ,
    (rawRatListSupportProduct acc xs).value =
      acc.value * (xs.map fun q ↦ if q = 0 then 1 else q).prod := by
  intro xs
  induction xs generalizing acc with
  | nil => simp [rawRatListSupportProduct]
  | cons q qs ih =>
      rw [rawRatListSupportProduct, ih, RawRat.value_mul,
        rawRatSupportFactor_value]
      simp only [List.map_cons, List.prod_cons]
      ring

end BeyondBethe
end
