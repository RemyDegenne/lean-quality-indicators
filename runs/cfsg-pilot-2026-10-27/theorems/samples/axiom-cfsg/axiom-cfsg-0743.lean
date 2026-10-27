public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.LocalAnalysis.GLTheoremA.S10

open scoped commutatorElement

namespace I161a

open CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Multiplier CFSG.Open

section TwE6Even

open CFSG.StandardType.TableB.TwE6

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

theorem two_pow_mod_three_of_even {n : ℕ} (hev : n % 2 = 0) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  rw [pow_mul]
  norm_num [Nat.pow_mod]

end TwE6Even
end I161a
end CFSG.LocalAnalysis.GLTheoremA
end
