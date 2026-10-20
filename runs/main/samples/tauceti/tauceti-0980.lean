public section

open Topology

namespace TauCeti

namespace Sym

variable {α : Type*} [TopologicalSpace α] {ι : Type*} [Fintype ι] {U : ι → Set α} {m : ι → ℕ}
  {n : ℕ}

theorem isOpenMap_sumSubtype (hU : ∀ i, IsOpen (U i)) (hn : ∑ i, m i = n) :
    IsOpenMap (sumSubtype U m hn) := by
  obtain ⟨e⟩ := nonempty_sigmaFinEquiv hn
  rw [isOpenQuotientMap_piMap_ofFn.isOpenMap_iff, sumSubtype_comp_piMap_ofFn hn e]
  exact isOpenMap_ofFn.comp (isOpenMap_regroup hU e)

end Sym
end TauCeti
end
