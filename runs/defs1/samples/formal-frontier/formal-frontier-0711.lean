public section

noncomputable section

namespace ContinuousGroupCohomology

universe uR uG uA

variable {R : Type uR} [CommRing R]

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Transport open-subgroup invariants by the ambient group action.

The containment has the source-to-target orientation: if
`V ≤ σ U σ⁻¹`, then `a ↦ σ • a` sends `A^U` to `A^V`. -/
@[expose] def openSubgroupInvariantsTransport (A : Rep.{uA} R G)
    (U V : OpenSubgroup G) (σ : G)
    (h : V.toSubgroup ≤ U.toSubgroup.map (MulAut.conj σ)) :
    openSubgroupInvariants A U →ₗ[R] openSubgroupInvariants A V where
  toFun x := ⟨A.ρ σ x, fun g ↦ by
    change A.ρ (g : G) (A.ρ σ x) = A.ρ σ x
    rw [← Representation.mem_stabilizer, A.ρ.stabilizer_conj σ x]
    exact (Subgroup.map_mono (fun u hu ↦ x.2 ⟨u, hu⟩)) (h g.2)⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

end ContinuousGroupCohomology
end
end
