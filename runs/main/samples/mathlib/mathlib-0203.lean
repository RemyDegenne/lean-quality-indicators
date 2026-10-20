@[expose] public section

open Finset

open scoped ComplexConjugate

namespace Complex

variable (x y : ℂ)

theorem cot_conj : cot (conj x) = conj (cot x) := by rw [cot, sin_conj, cos_conj, ← map_div₀, cot]

end Complex
end
