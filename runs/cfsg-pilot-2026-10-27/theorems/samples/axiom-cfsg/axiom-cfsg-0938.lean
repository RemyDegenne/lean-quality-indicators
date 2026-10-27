public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.Open CFSG.Quasithin.EmptyFaithfulMultiple.L1547

open CFSG.HardMathSupport.Cooperstein.StructureLie

variable {G : Type} [Group G]

theorem alt4_pow_six (g : alternatingGroup (Fin 4)) (h : g ^ 6 = 1) : g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  revert g; decide +kernel

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
end
