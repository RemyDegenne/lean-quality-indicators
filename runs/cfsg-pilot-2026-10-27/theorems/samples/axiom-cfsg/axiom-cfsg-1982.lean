public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism

open CFSG.Blueprint CFSG.LieType.Ree

open scoped commutatorElement

variable (a : ℕ) (K : Type) [Field K]

variable {a K}

theorem unipotentElt_zero_mem_suzukiZ0 (b : K) :
    (unipotentElt a K 0 b : suzukiGroup a K) ∈ suzukiZ0 a K :=
  Subgroup.subset_closure ⟨b, rfl⟩

end CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism
end
