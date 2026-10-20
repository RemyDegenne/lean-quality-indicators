public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable {N p : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

theorem heckeRingHomCharSpace_heckeTGeneratorGamma0 [NeZero N] (hp : p.Prime) :
    heckeRingHomCharSpace k χ (heckeTGeneratorGamma0 N p) =
      (heckeTNat k p (_hn := ⟨hp.ne_zero⟩)).restrict
        fun _ hf ↦ heckeTNat_mem_modFormCharSpace k χ hp hf :=
  LinearMap.ext fun f ↦ Subtype.ext (coe_heckeRingHomCharSpace_heckeTGeneratorGamma0 k χ hp f)

end HeckeRing.GL2
end
