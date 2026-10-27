@[expose] public section

universe u v

open CategoryTheory

attribute [instance] SemiRingCat.semiring

attribute [instance] RingCat.ring

attribute [instance] CommSemiRingCat.commSemiring

attribute [instance] CommRingCat.commRing

namespace CategoryTheory.Iso

/-- Build a `RingEquiv` from an isomorphism in the category `CommRingCat`. -/
def commRingCatIsoToRingEquiv {R S : CommRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

end CategoryTheory.Iso
end
