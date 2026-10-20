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

/-- The orbit-difference map as a continuous additive homomorphism. -/
def finiteOrbitDifferenceContinuousHom (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) :
    (Fin (Fintype.card H) → M) →ₜ+ M where
  toAddMonoidHom := (finiteOrbitDifference ρ).toAddMonoidHom
  continuous_toFun := by
    change Continuous (fun x : Fin (Fintype.card H) → M ↦
      ∑ i : Fin (Fintype.card H),
        ((ρ ((Fintype.equivFin H).symm i)) (x i) - x i))
    exact continuous_finsetSum Finset.univ fun i _ ↦
      ((hρ ((Fintype.equivFin H).symm i)).comp (continuous_apply i)).sub
        (continuous_apply i)

end Topology
end ContinuousGroupCohomology
end
end
