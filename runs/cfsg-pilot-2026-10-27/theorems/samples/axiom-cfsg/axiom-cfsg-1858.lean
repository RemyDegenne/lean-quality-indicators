public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.CentralExt

variable {r : ℕ} {k : Type} [Field k] {E : Type*} [Group E]

variable [Finite k] [Finite E] {π : E →* StatedSp r k}

section Identities

variable (hS : Hyp π)

include hS

theorem pi_vLift (i : Fin r) : π (vLift π i) = lam i sl2W := hS.map_lift _ _

end Identities
end CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
end
