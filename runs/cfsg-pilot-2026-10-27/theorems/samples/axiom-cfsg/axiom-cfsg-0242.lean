public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

section Linear

variable {E V : Type} [CommGroup E] [Finite E] [AddCommGroup V] [Finite V] [Module (ZMod 2) V]

theorem neg_eq_self_zmod2 (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, add_self_zmod2]

end Linear
end CFSG.LocalAnalysis.GLTheoremA.H1017
end
