namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace NeronModelInfra GoodReductionJacobian

namespace InfGroupLawA3

section Identities

variable {X Y Z : Scheme.{u}}

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)

noncomputable def π₂ := stalkMapOfEq (pullback.snd f f) (unitPair f L (IsLocalRing.closedPoint k))
  (unit f L (IsLocalRing.closedPoint k)) (snd_z f L)

end Identities
end InfGroupLawA3
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq
