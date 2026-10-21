namespace OAI

namespace Erdos970

open scoped _root_.Erdos970

namespace NumberTheoryLean.CanonicalKeyReplacement

open PrimeHistories CanonicalStopKey CanonicalKeyWitness ActualStopGroupFiber

open SourceStopPredicate ActualTagFreezing ActualFrozenStopFamily BinReplacementOrder

open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition

open ErdosInversePrimeBin ErdosInverseAlignment

variable {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
  {Y : ℕ} {Cs eta Clen B b₀ b₁ mu : ℝ} {a : ℕ → ℕ} {z : Node}
  {k : Key (binCount w top xi)} (d : Witness hw htop hxi Y Cs eta Clen B b₀ b₁ mu a z k)

include d

theorem search_lower : Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ lower w top xi k.tag.bin := by
  have hR : 0 < lower w top xi k.tag.bin := endpoint_pos (zero_lt_one.trans hw) k.tag.bin.1
  have hs : w^((1:ℝ)/4) ≤ Real.log (lower w top xi k.tag.bin)/Real.log w := d.search
  have hh := Real.exp_le_exp.mpr ((le_div_iff₀ (Real.log_pos hw)).mp hs)
  simpa only [Real.exp_log hR] using hh

end NumberTheoryLean.CanonicalKeyReplacement
end Erdos970
end OAI
