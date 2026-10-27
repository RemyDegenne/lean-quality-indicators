namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_forall_isUnit

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.style.multiGoal false

set_option linter.unusedSimpArgs false

set_option linter.style.longFile 0

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion

open IsDedekindDomain NumberField Filter Topology

noncomputable section

namespace KLICC

section Coord

variable {a b : ℚ}

def IsCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) : Prop :=
  ∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
    φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
      algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])

end Coord
end KLICC
end
end P2MW.S_QuaternionAlgebra_IsOrder_exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_forall_isUnit
