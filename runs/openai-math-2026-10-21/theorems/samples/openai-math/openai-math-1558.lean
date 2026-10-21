namespace OAI

namespace Erdos970

section

namespace ErdosRandomVariance

attribute [local instance] Classical.propDecidable

theorem pairKernel_diagonal (P : Finset ℕ) (i : ℕ) : pairKernel P i i = sieveProduct P := by
  unfold pairKernel sieveProduct
  apply Finset.prod_congr rfl
  intro p _
  simp only [congruenceIndicator, Nat.ModEq.refl, ite_true, mul_one]
  ring

end ErdosRandomVariance
end
end Erdos970
end OAI
