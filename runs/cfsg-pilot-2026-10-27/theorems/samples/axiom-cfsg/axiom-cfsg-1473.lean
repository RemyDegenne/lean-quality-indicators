public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module

section Field

variable {L : Type} [Field L] [Finite L] [Algebra (ZMod 2) L]

theorem swap_mul_torusPlus (u : Lˣ) :
    LinearEquiv.prodComm (ZMod 2) L L * torusPlus L u =
      torusPlus L u⁻¹ * LinearEquiv.prodComm (ZMod 2) L L := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [torusPlus_apply, LinearEquiv.prodComm_apply, Prod.swap, inv_inv]

end Field
end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
end
