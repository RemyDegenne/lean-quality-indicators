public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module

open scoped TensorProduct

open Representation

open CFSG.Open

open CFSG.QuasithinUnique.Setup.X7b (TwistEquiv)

open CFSG.Semidihedral.Principal (repMultiplicity_eq_add_of_exact)

open CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal (block)

section BaseChange

variable {K : Type} [Field K] [Fintype K] [CharP K 2] [Algebra (ZMod 2) K]
  {G : Type} [Group G] {N : Type} [AddCommGroup N] [Module (ZMod 2) N]

theorem baseChangeRep_apply (ρ : Representation (ZMod 2) G N) (g : G) :
    baseChangeRep (K := K) ρ g = (ρ g).baseChange K := rfl

end BaseChange
end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
end
