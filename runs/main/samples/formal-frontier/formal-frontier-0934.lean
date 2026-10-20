set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

theorem idealGeneralLinearGroupToRing_shortExact
    {R : Type u} [Ring R]
    {n : Type v} [Fintype n] [DecidableEq n]
    (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) :
    Function.Injective (idealGeneralLinearGroupToRing (n := n) I) ∧
      Function.MulExact (idealGeneralLinearGroupToRing (n := n) I)
        (mapRingHom (Ideal.Quotient.mk I.asIdeal) :
          GL n R →* GL n (R ⧸ I.asIdeal)) ∧
      Function.Surjective (mapRingHom (Ideal.Quotient.mk I.asIdeal) :
        GL n R →* GL n (R ⧸ I.asIdeal)) :=
  ⟨idealGeneralLinearGroupToRing_injective I,
    idealGeneralLinearGroupToRing_mulExact I,
    mapRingHom_quotient_surjective I hI⟩

end Matrix.GeneralLinearGroup
end
