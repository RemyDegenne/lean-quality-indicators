namespace P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField

set_option autoImplicit false

namespace HerbrandPortM

open IsLocalRing Polynomial IsDiscreteValuationRing

namespace IsDiscreteValuationRing

open IsDiscreteValuationRing IntermediateField

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

variable [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]

omit [Module.Finite A B] in

theorem residue_aeval_eq (G : A[X]) (x : B) :
    residue B (aeval x G) = aeval (residue B x) (G.map (residue A)) := by
  conv_rhs => rw [aeval_def, eval₂_map]
  rw [aeval_def, Polynomial.hom_eval₂]
  congr 1

end IsDiscreteValuationRing
end HerbrandPortM
end P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField
