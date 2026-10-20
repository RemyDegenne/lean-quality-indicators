@[expose] public section

open Set

variable {α : Type*}

namespace OrderIso

variable [LinearOrder α] {x y : α}

variable (x) in
/-- A linear order is isomorphic to the lexicographic sum of elements less than `x` and elements
greater or equal to `x`. -/
def sumLexIioIci : Iio x ⊕ₗ Ici x ≃o α :=
  (sumLexCongr (refl _) (Set.orderIsoOfEq (Ici x) {y | ¬ y < x} (by ext; simp))).trans <|
    ofRelIsoLT (RelIso.sumLexComplLeft (· < ·) x)

end OrderIso
end
