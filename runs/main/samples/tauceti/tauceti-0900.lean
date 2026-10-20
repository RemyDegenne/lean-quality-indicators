public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] (k : ℤ)
  (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

@[simp] lemma coe_heckeSlashGamma0CuspFormEnd (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ⇑(heckeSlashGamma0CuspFormEnd k D f) = heckeSlashSum k D f :=
  coe_heckeSlashCuspFormEnd k D (out_mem_glpos_of_delta0 N D) f

end HeckeRing.GL2
end
