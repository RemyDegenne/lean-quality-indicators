namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_forall_isBaseChangeAlong_away_of_overlap

set_option autoImplicit false

open scoped TensorProduct

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B24D

section Loc

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B]

variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]

theorem isLocalizedModule_ιB (S : Submonoid B) [IsLocalization S A] (N : FullLattice 𝒪 K) :
    IsLocalizedModule S (ιB (𝒪 := 𝒪) A N) :=
  (isLocalizedModule_iff_isBaseChange S A _).mpr
    (IsBaseChange.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 B A A (↥N.1))
      (fun p => cancelBaseChange_one_tmul (IsScalarTower.toAlgHom 𝒪 B A) (fun _ => rfl) N p))

end Loc
end B24D
end P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_forall_isBaseChangeAlong_away_of_overlap
