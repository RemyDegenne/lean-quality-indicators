public section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

open CFSG.Monster.B.Classical.UnitarySix (bar bar_add bar_mul bar_bar bar_zero bar_one
  mul_bar_of_ne_zero)

theorem isSimpleGroup_unitaryPSU : IsSimpleGroup (unitaryPSU hF4 6) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F4 2 1 natCard_F4 6
    (by norm_num) (by decide)
  exact (unitaryPSUEquiv hF4 (n := 6) (by norm_num)).isSimpleGroup

end CFSG.Monster.B.TwoA.Unitary
end
