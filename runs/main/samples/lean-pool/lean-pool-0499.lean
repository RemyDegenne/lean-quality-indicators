@[expose] public section

open scoped ComplexOrder

namespace Matrix

variable {n 𝕜 : Type _} [Fintype n]

section

variable [Field 𝕜] [StarRing 𝕜]

theorem _root_.Matrix.unitaryGroup.coe_hMul_star_self [DecidableEq n]
    (a : Matrix.unitaryGroup n 𝕜) :
    (HMul.hMul a (star a) : Matrix n n 𝕜) = (1 : Matrix n n 𝕜) := by
  simp_all

end
end Matrix
end
