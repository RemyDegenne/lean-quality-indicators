namespace OAI

noncomputable section

namespace LaughlinGap.RealOccupation

open scoped BigOperators ComplexOrder

open Spin

namespace Certificate19

lemma cover_10 : ∀ j : Fin 5, ∀ x : Fin 5,
  (fourTermLabels (by omega : 19 ≤ 23) ⟨10,j,x⟩).Nodup →
    (fourTermLabels (by omega : 19 ≤ 23) ⟨10,j,x⟩).toFinset=keys (keyIndex 10 j x) := by decide +kernel

end Certificate19
end LaughlinGap.RealOccupation
end
end OAI
