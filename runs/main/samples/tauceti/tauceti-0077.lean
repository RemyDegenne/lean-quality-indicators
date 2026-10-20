public section

open scoped Matrix

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace MinusculeWeightTable

variable {B ι : Type*} (T : MinusculeWeightTable B ι)

@[simp]
theorem weight_reflection_self (i : B) (a : ι) :
    T.weight (T.reflection i a) i = -T.weight a i := by
  rw [T.weight_reflection, T.cartanMatrix_diag]
  ring

end MinusculeWeightTable
end TauCeti
end
