public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

open scoped commutatorElement

namespace Std4r1

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem Pz_eq (h : Std4r1 G z S K F) : Pz S z = S ⊓ K := by
  unfold Pz; rw [h.rigidProduct_eq]

end Std4r1
end CFSG.GH74.GLS.Stage1.Thm3.Sec6
end
