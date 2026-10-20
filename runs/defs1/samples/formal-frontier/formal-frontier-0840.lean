@[expose] public section

universe u v

namespace Algebra.GrothendieckAddGroup

section RingLifts

variable {A : Type u} {S : Type v} [Semiring A] [Ring S]

/-- Extend a ring homomorphism to the additive Grothendieck group, retaining its
additive lift. -/
noncomputable def liftRingHom (f : A →+* S) : GrothendieckAddGroup A →+* S :=
  { lift f.toAddMonoidHom with
    map_one' := by
      change lift f.toAddMonoidHom (of (1 : A)) = (1 : S)
      exact (lift_of f.toAddMonoidHom (1 : A)).trans f.map_one
    map_mul' := by
      apply (AddMonoidHom.map_mul_iff (lift f.toAddMonoidHom)).mpr
      apply hom_ext₂
      intro a b
      change lift f.toAddMonoidHom (mulAddHom (of a) (of b)) =
        lift f.toAddMonoidHom (of a) * lift f.toAddMonoidHom (of b)
      simp only [mulAddHom_of, lift_of]
      exact f.map_mul a b }

end RingLifts
end Algebra.GrothendieckAddGroup
end
