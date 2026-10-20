@[expose] public section

universe u v

open CategoryTheory

attribute [instance] SemiRingCat.semiring

attribute [instance] RingCat.ring

namespace RingCat

/-- Ring equivalences are isomorphisms in category of rings -/
@[simps]
def _root_.RingEquiv.toRingCatIso {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm

end RingCat
end
