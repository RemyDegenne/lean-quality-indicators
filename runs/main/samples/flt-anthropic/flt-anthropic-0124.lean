namespace P2MW.S_TateCurve_ks17_D3_exports

open scoped NNReal

p2m_open

universe u_1 u_2

namespace TateCurve

p2m_open

theorem sum_mul_Fz_Fz_eq_sum_lines_nat : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g h : α → ℕ)
    {N : ℕ} (hg : ∀ x ∈ S, g x ≤ N) (hh : ∀ x ∈ S, h x ≤ N),
      ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v (h x : ℤ) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => g x = k ∧ h x = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ) :=
  TateCurve.ks17_C3_exports.{u_1, u_2}.2.1

end TateCurve
end P2MW.S_TateCurve_ks17_D3_exports
