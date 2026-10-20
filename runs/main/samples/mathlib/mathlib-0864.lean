@[expose] public section

noncomputable section

open scoped NNReal Nat

open Finset

section Seminorm

universe u wE wF wG v

variable {𝕜 : Type u} {n : ℕ} {E : Type wE} {F : Type wF} {G : Type wG} {ι : Type v}
  [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace ContinuousAlternatingMap

variable [Fintype ι] {f : E [⋀^ι]→L[𝕜] F} {m : ι → E}

theorem le_mul_prod_of_opNorm_le_of_le
    {m : ι → E} {C : ℝ} {b : ι → ℝ} (hC : ‖f‖ ≤ C) (hm : ∀ i, ‖m i‖ ≤ b i) :
    ‖f m‖ ≤ C * ∏ i, b i :=
  f.1.le_mul_prod_of_opNorm_le_of_le hC hm

end ContinuousAlternatingMap
end Seminorm
end
end
