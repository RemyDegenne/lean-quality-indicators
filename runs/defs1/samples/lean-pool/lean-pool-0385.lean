@[expose] public section

open Complex Real Filter Topology MeasureTheory

open scoped BigOperators ComplexConjugate

namespace Hadamard

/-- **Definition 1.1**: The order of growth of an entire function

Definition: The infimum of ρ₀ such that |f(z)| < exp(|z|^ρ₀) for |z| ≥ R₀

Lemma 1.2. Let f be an entire function of finite order.
  ρ(f) = lim sup_{r≥R→∞} (log log M(f,r)) / log(r)
where M(f,r) = max_{|z|=r} |f(z)|
-/
noncomputable def order (f : ℂ → ℂ) : ℝ :=
  Filter.limsup (fun r : ℝ =>
    if r > 0 ∧ maxModulus f r > 1 then
      Real.log (Real.log (maxModulus f r)) / Real.log r
    else 0) Filter.atTop

end Hadamard
end
