public section

universe u v

open Finset NNReal ENNReal

noncomputable section

variable {ι : Type u} (s : Finset ι)

namespace Real

lemma add_rpow_le_rpow_add {p : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp1 : 1 ≤ p) :
     a ^ p + b ^ p ≤ (a + b) ^ p := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.add_rpow_le_rpow_add a b hp1

end Real
end
end
