namespace OAI

noncomputable section

open scoped BigOperators

open scoped BigOperators Matrix

open scoped Matrix

open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.InfiniteChains.Cone

open Attachment

variable {V : Type} [DecidableEq V]

variable {G : Type} [Group G] [MulAction G V]

open scoped Pointwise

@[simp] lemma pull_inv (g : G) (f : Finset V → k) : pull g (pull g⁻¹ f) = f := by
  funext s
  simp [pull]

end CoboundaryExpanders.InfiniteChains.Cone
end
end OAI
