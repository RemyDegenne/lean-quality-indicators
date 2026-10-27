public section

namespace TauCeti

open Pointwise Topology

variable {E X A : Type*} {G : Type*} [Group G] [MulAction G E] [MulAction G A] {q : E → X}

namespace BalancedProduct

/-- The balanced product with the left regular action of `G` recovers `E`.
The class of `(e, g)` is sent to `g⁻¹ • e`. -/
def equivSelf : BalancedProduct G E G ≃ E where
  toFun := Quotient.lift (fun p : E × G => p.2⁻¹ • p.1) fun _ _ ⟨g, hg⟩ => by
    rw [← hg]
    simp [mul_smul]
  invFun e := mk G e 1
  left_inv z := by
    induction z using Quotient.inductionOn with
    | h p => simp
  right_inv e := by simp

end BalancedProduct
end TauCeti
end
