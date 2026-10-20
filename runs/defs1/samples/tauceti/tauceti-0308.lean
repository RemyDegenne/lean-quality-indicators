public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm Manifold

namespace HeckeRing.GL2

variable {N p : ℕ} (k : ℤ)

variable [NeZero N]

/-- **The upper-triangular Hecke operator on `M_k(Γ₁(N))`**, for `p ∣ N`, as a `ℂ`-linear
endomorphism. Bundling is what lets Hecke operators compose and later carry a ring structure. -/
noncomputable def heckeSlashUpperTriModularFormEnd (hpN : p ∣ N) :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := heckeSlashUpperTriModularForm k hpN
  map_add' f g := by
    ext τ; simp [coe_heckeSlashUpperTriModularForm, heckeSlashUpperTri_add]
  map_smul' c f := by
    ext τ; simp [coe_heckeSlashUpperTriModularForm, heckeSlashUpperTri_smul]

end HeckeRing.GL2
end
