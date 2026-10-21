namespace OAI

namespace Release061

open Set Filter Topology

open Set Filter Metric MeasureTheory

open scoped Topology

open Polynomial

open Polynomial Algebra

open scoped nonZeroDivisors

open Polynomial Algebra

theorem fiberPolynomial_eval_eq_zero {X Y : Type*} (π : X → Y)
    (hfin : ∀ y, (π ⁻¹' {y}).Finite) (h : X → ℂ) (x : X) :
    (fiberPolynomial π hfin h (π x)).eval (h x) = 0 := by
  classical
  unfold fiberPolynomial
  rw [eval_prod]
  apply Finset.prod_eq_zero ((hfin (π x)).mem_toFinset.mpr (show x ∈ π ⁻¹' {π x} from rfl))
  simp

end Release061
end OAI
