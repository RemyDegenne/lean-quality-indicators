public section

namespace CFSG.ClassicalInvolution.Nobq

open Matrix CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter

theorem outTwoCyclic_psl2_of_charTwo (K : Type) [Field K] [Finite K] [CharP K 2] :
    OutTwoCyclic (PSL2 K) := by
  have := isCyclic_outer_psl2_of_charTwo K
  intro P _
  exact Subgroup.isCyclic P

end CFSG.ClassicalInvolution.Nobq
end
