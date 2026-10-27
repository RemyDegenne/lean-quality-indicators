public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace OctFrame

variable {T : TitsSystem G 8} (F : OctFrame T)

theorem xo_one (x : G) : F.xo 1 x = x := by
  simp [OctFrame.xo]

end OctFrame
end CFSG.GH74.Tits83
end
