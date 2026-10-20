@[expose] public section

section SourcePromiseDefs

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {σ : Type*} [DecidableEq σ]

variable {X : Type*} [Fintype X] [DecidableEq X]

variable {O : Type*}

variable [DecidableEq O]

omit [DecidableEq ι] in
theorem advPMOn_le_of_dualPairOn {K : Type*} [Fintype K] {read : X → ι → σ}
    {f : X → O} (P : DualPairOn read K f) {c : ℝ} (hc : 0 ≤ c)
    (hP : P.IsCostLe c) : advPMOn read f ≤ c := by
  classical
  refine advPMOn_le fun Γ hΓ hΓD => ?_
  refine l2_opNorm_le_of_forall_dotProduct Γ hc fun a b => ?_
  have hsplit : ∀ x y, a x * Γ x y * b y
      = ∑ p : ι × K, (a x * P.u x p.1 p.2) * (Γ ⊙ advDOn read p.1) x y *
          (b y * P.v y p.1 p.2) := by
    intro x y
    rw [Fintype.sum_prod_type]
    change a x * Γ x y * b y
      = ∑ i, ∑ k, (a x * P.u x i k) * (Γ ⊙ advDOn read i) x y * (b y * P.v y i k)
    have hstep : ∀ i : ι,
        (∑ k, (a x * P.u x i k) * (Γ ⊙ advDOn read i) x y * (b y * P.v y i k))
        = (a x * b y * Γ x y) *
            (if read x i = read y i then 0 else ∑ k, P.u x i k * P.v y i k) := by
      intro i
      by_cases hi : read x i = read y i
      · rw [ite_eq_left hi, mul_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hadamard_advDOn_apply, ite_eq_left hi]
        ring
      · rw [ite_eq_right hi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hadamard_advDOn_apply, ite_eq_right hi]
        ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
      ← Finset.mul_sum, P.constraint x y]
    by_cases hg : f x = f y
    · rw [ite_eq_left hg, hΓ.2 x y hg]
      ring
    · rw [ite_eq_right hg]
      ring
  have hexpand : a ⬝ᵥ Γ *ᵥ b
      = ∑ p : ι × K, (fun x => a x * P.u x p.1 p.2) ⬝ᵥ
          (fun i => Γ ⊙ advDOn read i) p.1 *ᵥ (fun y => b y * P.v y p.1 p.2) := by
    rw [dotProduct_mulVec_eq_sum]
    have hrhs : (∑ p : ι × K, (fun x => a x * P.u x p.1 p.2) ⬝ᵥ
        (fun i => Γ ⊙ advDOn read i) p.1 *ᵥ (fun y => b y * P.v y p.1 p.2))
        = ∑ p : ι × K, ∑ x, ∑ y, (a x * P.u x p.1 p.2) *
            (Γ ⊙ advDOn read p.1) x y * (b y * P.v y p.1 p.2) :=
      Finset.sum_congr rfl fun p _ => dotProduct_mulVec_eq_sum _ _ _
    rw [hrhs]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => hsplit x y
  rw [hexpand]
  exact key_bound (fun i => Γ ⊙ advDOn read i) hΓD a b P.u P.v hc hP.1 hP.2

end QuantumQueryComplexity
end SourcePromiseDefs
end
