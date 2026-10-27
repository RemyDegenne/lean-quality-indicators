@[expose] public section

noncomputable section

open scoped NNReal ENNReal Function

variable {𝕜 𝕜' : Type*} {α : Type*} {E : α → Type*} {p q : ℝ≥0∞} [∀ i, NormedAddCommGroup (E i)]

@[inherit_doc] scoped[lp] notation "ℓ^" p "(" ι ", " E ")" => lp (fun _ : ι ↦ E) p

scoped[lp] notation "ℓ⁰(" ι ", " E ")" => lp (fun _ : ι ↦ E) 0

scoped[lp] notation "ℓ¹(" ι ", " E ")" => lp (fun _ : ι ↦ E) 1

scoped[lp] notation "ℓ²(" ι ", " E ")" => lp (fun _ : ι ↦ E) 2

namespace lp

variable (E p)

variable {E p}

section Algebra

variable {I : Type*} {B : I → Type*}

variable [NormedField 𝕜] [∀ i, NormedRing (B i)] [∀ i, NormedAlgebra 𝕜 (B i)]

variable [∀ i, NormOneClass (B i)]

variable (𝕜 B)

/-- The `𝕜`-subalgebra of elements of `∀ i : α, B i` whose `lp` norm is finite. This is `lp E ∞`,
with extra structure. -/
def _root_.lpInftySubalgebra : Subalgebra 𝕜 (PreLp B) :=
  { lpInftySubring B with
    carrier := { f | Memℓp f ∞ }
    algebraMap_mem' := algebraMap_memℓp_infty }

end Algebra
end lp
end
end
