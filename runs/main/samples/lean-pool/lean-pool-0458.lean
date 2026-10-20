@[expose] public section

universe u v v₁ v₂ w

variable (K : Type u) [Field K]

variable (A B : Type u) [Ring A] [Ring B] [Algebra K A] [Algebra K B]

open scoped TensorProduct

variable {K : Type u} [Field K]

namespace BrauerGroup

open IsBrauerEquivalent

lemma mul_inv (A : CSA.{u, u} K) : IsBrauerEquivalent (mul A (inv (K := K) A)) oneIn' := by
  unfold mul inv oneIn'
  let n := Module.finrank K A
  have hn : NeZero n := ⟨Module.finrank_pos.ne'⟩
  have := tensorSelfOp K A
  exact ⟨1, n, one_ne_zero, hn.1, ⟨dimOneIso _|>.trans this⟩⟩

end BrauerGroup
end
