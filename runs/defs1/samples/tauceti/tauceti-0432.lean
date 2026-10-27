public section

namespace TauCeti.GaloisLatticeCat

universe u

variable {k : Type u} [Field k]

attribute [local instance] TauCeti.GaloisLatticeCat.storedModule

/-- The automorphism group of the action field maps to the faithful finite quotient acting on the
lattice. -/
noncomputable def actionFieldToActionQuotient (M : GaloisLatticeCat k) :
    Gal(actionField M / k) →* actionQuotient M :=
  (QuotientGroup.lift (actionFieldRestriction M).ker
      (QuotientGroup.mk' M.obj.ρ.ker) (by
        intro σ hσ
        rw [QuotientGroup.ker_mk']
        exact actionFieldRestriction_ker_le M hσ)).comp
    (QuotientGroup.quotientKerEquivOfSurjective (actionFieldRestriction M)
      (actionFieldRestriction_surjective M)).symm.toMonoidHom

end TauCeti.GaloisLatticeCat
end
