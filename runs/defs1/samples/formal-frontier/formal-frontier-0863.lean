@[expose] public section

universe u v

namespace Algebra.GrothendieckAddGroup

section RingLifts

variable {A : Type u} {S : Type v} [Semiring A] [Ring S]

/-- The ring-homomorphism universal property of the additive Grothendieck group,
with restriction along `ofRingHom` as its inverse. -/
noncomputable def liftRingEquiv : (A →+* S) ≃ (GrothendieckAddGroup A →+* S) where
  toFun := liftRingHom
  invFun F := F.comp (ofRingHom A)
  left_inv f := by
    apply RingHom.ext
    intro a
    exact liftRingHom_of f a
  right_inv F := by
    apply ringHom_ext
    intro a
    exact liftRingHom_of (F.comp (ofRingHom A)) a

end RingLifts
end Algebra.GrothendieckAddGroup
end
