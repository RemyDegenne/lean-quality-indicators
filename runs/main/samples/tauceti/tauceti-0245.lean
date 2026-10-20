public section

namespace TauCeti

open Function Set

namespace DynkinType

namespace TypeC

variable {n : ℕ}

lemma dotProduct_pairCoroot_left {p q : Signed n} (h : q ≠ signedNeg p) :
    signedWeight p ⬝ᵥ pairCoroot p q = 1 := by
  rcases eq_or_ne p q with rfl | hne
  · rw [pairCoroot, ite_eq_left rfl, signedWeight_dotProduct_self]
  · rw [pairCoroot, ite_eq_right hne, dotProduct_add, signedWeight_dotProduct_self,
      signedWeight_dotProduct_eq_zero hne (ne_signedNeg_of_ne_signedNeg h), add_zero]

end TypeC
end DynkinType
end TauCeti
end
