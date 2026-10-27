public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace OrdPNS

section Conj

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {m f : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

omit [Finite G] [Finite F] [CharP F 2] in
theorem conj_psi (u v : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    (ψ u)⁻¹ * ψ v * ψ u = ψ (InnerDiagA.conjSL (Matrix.SpecialLinearGroup.toGL u⁻¹) v) := by
  have h : InnerDiagA.conjSL (Matrix.SpecialLinearGroup.toGL u⁻¹) v = u⁻¹ * v * u := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [RootPlaneA.toGL_conjSL, map_mul, map_mul, map_inv, inv_inv]
  rw [h, map_mul, map_mul, map_inv]

end Conj
end OrdPNS
end CFSG.StandardType
end
