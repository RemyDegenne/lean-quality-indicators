@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.taum.primeprime.def` (1130-1136), for `m ≥ 1`:
`τ''_m := 2⁻²⁵ ⌈a_{m-1} / ε_{m-1}^{2δ}⌉⁻¹`. The value at `m = 0` is unused. -/
def tauPP (β : ℝ) (Λ : ℕ) (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (-25 : ℤ) *
    ((⌈a β Λ (m - 1) / epsilon β Λ (m - 1) ^ (2 * delta β)⌉₊ : ℕ) : ℝ)⁻¹

end AVenhance
end
end
