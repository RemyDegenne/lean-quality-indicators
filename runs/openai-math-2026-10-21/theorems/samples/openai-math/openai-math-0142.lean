namespace OAI

section

section

open Filter

open scoped BigOperators Topology

open InnerProductSpace

open scoped InnerProductSpace

open scoped BigOperators Matrix.Norms.L2Operator

open scoped BigOperators NNReal

open Matrix

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_leading_of_rowsums (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a b : ℝ) (hb : 0 ≤ b)
    (hlower : ∀ i, a ≤ ∑ j, A i j) (hupper : ∀ i, ∑ j, |A i j| ≤ b) :
    ∃ i₀, a ≤ hA.eigenvalues i₀ ∧ |hA.eigenvalues i₀| ≤ b ∧
      ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₀ := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ hA.eigenvalues
    Finset.univ_nonempty
  have hm : ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₀ := fun i => hi₀ i (Finset.mem_univ i)
  refine ⟨i₀, ?_, eigenvalue_abs_le_rowsum A hA b hb hupper i₀, hm⟩
  have hpos := (hermitian_upper_posSemidef A hA (hA.eigenvalues i₀) hm).dotProduct_mulVec_nonneg (fun _ => 1)
  have heval : (star (fun _ : ι => (1 : ℝ))) ⬝ᵥ
      ((hA.eigenvalues i₀ • 1 - A) *ᵥ fun _ => 1) =
      (Fintype.card ι : ℝ) * hA.eigenvalues i₀ - ∑ i, ∑ j, A i j := by
    simp [dotProduct, Finset.sum_sub_distrib, Matrix.mulVec, Matrix.one_apply]
  rw [heval] at hpos
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlower i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hl
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith

end SharpTerminalLeave
end
end
end OAI
