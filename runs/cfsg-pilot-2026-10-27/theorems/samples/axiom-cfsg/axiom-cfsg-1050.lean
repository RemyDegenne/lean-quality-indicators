public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.LocalAnalysis.GLTheoremA.S10

open scoped commutatorElement

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem comm_primeCore_bot_of_qs {X M : Subgroup G} (hp : p.Prime) (hM : GLAPComponent p X M)
    (hq : CFSG.Open.IsQuasisimple ↥M) : Xc p M = ⊥ :=
  S9.commutator_eq_bot_of_isQuasisimple hp hM hq

end S12
end CFSG.LocalAnalysis.GLTheoremA
end
