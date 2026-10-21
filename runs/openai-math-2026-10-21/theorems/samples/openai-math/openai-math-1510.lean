namespace OAI

noncomputable section

open scoped BigOperators

open Finset

namespace KServer.PriorityKeys

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I Y:Type*} [Fintype I] [LinearOrder I] {A:I→Type*}

lemma key_congr_point (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y)
    (h:∀ i,q₀ i x=q₁ i x) : key q₀ x=key q₁ x := by
  simp only [key,selected_congr_point q₀ q₁ x h]

end KServer.PriorityKeys
end
end OAI
