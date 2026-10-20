@[expose] public section

universe u v

open CategoryTheory

attribute [instance] SemiRingCat.semiring

attribute [instance] RingCat.ring

namespace RingCat

lemma coe_of (R : Type u) [Ring R] : (of R : Type u) = R :=
  rfl

end RingCat
end
