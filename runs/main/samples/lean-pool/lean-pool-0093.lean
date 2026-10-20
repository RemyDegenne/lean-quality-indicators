@[expose] public section

namespace Egrs75.ClearingP3

open Nat

open Egrs75

open Egrs75.LeafInduction

open Egrs75.RepairDV

open Egrs75.RepairPaperfaithful

theorem lowDigits_half_pred_pow {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) (m : ℕ) :
    LowDigits p ((p ^ m - 1) / 2) := by
  induction m with
  | zero => simpa using RoundUp.lowDigits_zero p
  | succ k ih =>
    rw [half_pred_pow_succ (by omega) hodd k]
    exact RoundUp.lowDigits_cons (by omega) (le_refl _) ih

end Egrs75.ClearingP3
end
