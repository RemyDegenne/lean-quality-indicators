public section

namespace CFSG.GH74.GLS.Stage2.OddAut.BlockTorus

open Module Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section SLE2

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

theorem coe_mkSL (f : SLE K p s) :
    (mkSL K p s f : Matrix (Fin (4 + s)) (Fin (4 + s)) K) =
      (ΦA K p s).symm (f.1 : Module.End K (Em K p s)) := rfl

end SLE2
end CFSG.GH74.GLS.Stage2.OddAut.BlockTorus
end
