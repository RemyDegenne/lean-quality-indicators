namespace OAI

namespace JointDickman

open Finset

theorem residue_quotient_mean {d q : ℕ} [NeZero d] [NeZero q]
    (hd : d ∣ q) (F : ZMod d → ℝ) :
    (∑ a : ZMod q, F (a.val : ZMod d)) / (q : ℝ) =
      (∑ a : ZMod d, F a) / (d : ℝ) := by
  have hs := residue_sum_eq_range (fun a : ZMod q => (F (a.val : ZMod d) : ℂ))
  have hs' : (∑ a : ZMod q, F (a.val : ZMod d)) = ∑ n ∈ range q, F n := by
    have hn (n : ℕ) (hn : n ∈ range q) : (n : ZMod q).val = n :=
      ZMod.val_natCast_of_lt (mem_range.mp hn)
    have hr : (∑ n ∈ range q, F ((n : ZMod q).val : ZMod d)) =
        ∑ n ∈ range q, F n := sum_congr rfl (fun n hn' => by rw [hn n hn'])
    exact (by exact_mod_cast hs : (∑ a : ZMod q, F (a.val : ZMod d)) =
      ∑ n ∈ range q, F ((n : ZMod q).val : ZMod d)).trans hr
  rw [hs']
  exact periodic_mean_at_multiple (NeZero.pos q) hd F

end JointDickman
end OAI
