@[expose] public section

open Zeta32.Arith.Local

open Polynomial

open scoped BigOperators

namespace Zeta32.Outer

noncomputable section

theorem det_mul_GV2 (p : ℕ) [Fact p.Prime] {h : ℕ} {I : Type*} [Fintype I]
    (W : Matrix (Fin h) I ℚ[X]) (Cm : Matrix I (Fin h) ℚ[X]) (ρ : I → ℚ) (τ : Fin h → ℚ)
    (hW : ∀ a i, GV p (W a i) 0) (hC : ∀ i b, GV p (Cm i b) (ρ i + τ b)) (Bd : ℚ)
    (hB : ∀ f : Fin h → I, Function.Injective f → Bd ≤ ∑ b, ρ (f b)) :
    GV p (W * Cm).det (Bd + ∑ b, τ b) := by
  classical
  rw [det_mul_expand]
  apply GV.sum
  intro f _
  by_cases hf : Function.Injective f
  · have hprod : GV p (∏ b, Cm (f b) b) (∑ b, (ρ (f b) + τ b)) := GV.prod _ fun b _ => hC (f b) b
    have hdet : GV p (Matrix.of fun a b => W a (f b)).det (∑ _a : Fin h, (0:ℚ) + ∑ _b : Fin h,
      (0:ℚ)) :=
      det_GV (p := p) _ (fun _ => 0) (fun _ => 0) fun a b => by simpa using hW a (f b)
    simp only [Finset.sum_const_zero, add_zero] at hdet
    refine (hprod.mul hdet).mono ?_
    rw [Finset.sum_add_distrib, add_zero]
    linarith [hB f hf]
  · rw [det_cols_eq_zero W f hf, mul_zero]
    exact GV.zero _

end
end Zeta32.Outer
end
