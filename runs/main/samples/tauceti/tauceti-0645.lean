public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] (k : ℤ) (g : ↥(Gamma0 N))

theorem heckeSlashGamma1CuspFormEnd_diamondCosetGamma1_apply_of_mem_cuspFormCharSpace
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    heckeSlashGamma1CuspFormEnd k (diamondCosetGamma1 N g) f =
      (↑(χ ((Gamma0Map N).toHomUnits g)) : ℂ) • f := by
  rw [heckeSlashGamma1CuspFormEnd_diamondCosetGamma1]
  exact diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ _ hf

end HeckeRing.GL2
end
