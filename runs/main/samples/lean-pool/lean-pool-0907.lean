@[expose] public section

open Finset

namespace KasamiCyclicAdditive.Phase

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

section PowD

variable {m D : ℕ}

lemma sum_psi_mul_powD {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (hm : m ≠ 0) (hD : D ≠ 0) (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) (C : K) :
    ∑ y : K, ψ (C * y ^ D) = if C = 0 then (Fintype.card K : ℂ) else 0 := by
  have hbij := (powD_bijective (m := m) hm hD hmD (K := K))
  have h2 : ∑ y : K, ψ (C * y ^ D) = ∑ x : K, ψ (C * x) :=
    Fintype.sum_bijective _ hbij _ _ (fun y => rfl)
  rw [h2]
  simpa [mul_comm] using AddChar.sum_mulShift (R := K) (R' := ℂ) C hψ

end PowD
end KasamiCyclicAdditive.Phase
end
