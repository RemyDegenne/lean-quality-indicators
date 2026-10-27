public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open scoped commutatorElement

theorem l154_sq_eq_one_char_two {F : Type} [Field F] (h2 : (2 : F) = 0) {c : F} (hc : c ^ 2 = 1) : c = 1 := by
  have h : (c - 1) ^ 2 = 0 := by linear_combination hc + (1 - c) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)

end CFSG.LocalAnalysis.GLTheoremA.K155X
end
