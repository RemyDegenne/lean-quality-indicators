public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.ASVolI.ChH

open scoped Pointwise

theorem stmt8_4_of
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24T c))
    (hlu : Stmt5_LineU) : Stmt8_4 :=
  stmt8_4_of_fixOct fixOctPerfect_holds fixOctSym_holds fixOctCommW11_holds hres hlu

end CFSG.Quasithin.H13.AS91
end
