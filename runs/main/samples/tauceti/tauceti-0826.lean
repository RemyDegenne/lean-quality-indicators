public section

open MulAction Set UpperHalfPlane

open TauCeti.Subgroup.CuspDatum

open scoped MatrixGroups OnePoint Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n) {Γ : Subgroup PSL(2, ℝ)}

namespace SidePairing

variable {P} (σ : P.SidePairing)

theorem isCuspPoint_of_vertex_eq_inr {j : Fin n} {ξ : OnePoint ℝ} (hj : P.vertex j = .inr ξ)
    (hcycle : σ.cycleMap j ∈ Γ) (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    Γ.IsCuspPoint ξ :=
  Subgroup.isCuspPoint_iff_exists_mem_stabilizer_isParabolic.mpr
    ⟨⟨σ.cycleMap j, hcycle⟩, σ.cycleMap_smul_eq_self_of_vertex_eq_inr hj,
      σ.isParabolic_cycleMap_of_locallyFinite hj hcycle hlf⟩

end SidePairing
end TauCeti.UpperHalfPlane.ConvexPolygon
end
