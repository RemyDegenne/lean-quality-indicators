@[expose] public section

open Filter

open scoped Manifold ContDiff MatrixGroups Topology

variable {n : ℕ∞ω}

namespace UpperHalfPlane

lemma contMDiff_denom (g : GL (Fin 2) ℝ) : CMDiff n (fun τ : ℍ ↦ denom g τ) :=
  (contMDiff_const.mul contMDiff_coe).add contMDiff_const

end UpperHalfPlane
end
