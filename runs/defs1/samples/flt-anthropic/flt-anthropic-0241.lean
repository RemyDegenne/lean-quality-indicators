set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell.CubicInduction

section AdditiveJacquet

variable (v : HeightOneSpectrum (𝓞 ℚ))

def translateRepStep :
    Representation ℂ (Multiplicative (v.adicCompletion ℚ)) ↥(stepFunctions v) where
  toFun y := (translateFn v (Multiplicative.toAdd y)).restrict
    fun φ hφ => translateFn_mem_stepFunctions v (Multiplicative.toAdd y) hφ
  map_one' := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
    simp [LinearMap.restrict_apply]
  map_mul' y z := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
    simp [LinearMap.restrict_apply, add_assoc]

end AdditiveJacquet
end LanglandsTunnell.CubicInduction
end
