public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap

open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

section Plane

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} {θ : F →+* F} {σ : OW F → OW F}

theorem SemiInvol.proj0_invol (h : SemiInvol b c θ σ) (he : σ (eV F idx0) = eV F idx0) {v : OW F}
    (hv : v (Sum.inl idx0) = 0) : proj0 (σ (proj0 (σ v))) = v := by
  set P := σ (proj0 (σ v)) with hP
  have h1 := eq_proj0_add (σ v)
  have h2 := congrArg σ h1
  rw [h.invol, h.add, h.smul, he] at h2
  rw [← hP] at h2
  have h3 := congrArg proj0 h2
  rw [proj0_add, proj0_smul_eV, add_zero, proj0_of_apply_eq_zero hv] at h3
  exact h3.symm

end Plane
end CFSG.LocalAnalysis.RankThreeUC
end
