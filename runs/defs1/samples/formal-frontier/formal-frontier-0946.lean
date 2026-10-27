public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology

universe uR uH uM

variable {R : Type uR} [CommRing R]

variable {H : Type uH} [Group H] [Fintype H]

variable {M : Type uM} [AddCommGroup M] [Module R M]

section Topology

variable [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M]
  [T2Space M]

variable {N : Type uM} [AddCommGroup N] [Module R N]
  [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [T2Space N]

/-- A continuous invariant linear map out of a finite-group representation
descends continuously to its compact coinvariants. -/
@[expose] def finiteCoinvariantsDesc (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) (f : M →ₗ[R] N)
    (hf : Continuous f) (hinv : ∀ g : H, f ∘ₗ ρ g = f) :
    finiteCoinvariants ρ hρ ⟶ CompHausAddCommGrp.of N := by
  apply ConcreteCategory.ofHom
  refine
    { toAddMonoidHom :=
        (Representation.Coinvariants.lift ρ f hinv).toAddMonoidHom
      continuous_toFun := ?_ }
  exact continuous_coinduced_dom.2 hf

end Topology
end ContinuousGroupCohomology
end
end
