@[expose] public section

universe u v

namespace Algebra.GrothendieckAddGroup

section RingLifts

variable {A : Type u} {S : Type v} [Semiring A] [Ring S]

@[ext]
theorem ringHom_ext {F G : GrothendieckAddGroup A →+* S}
    (h : ∀ a : A, F (of a) = G (of a)) : F = G := by
  apply RingHom.coe_addMonoidHom_injective
  exact hom_ext h

end RingLifts
end Algebra.GrothendieckAddGroup
end
