@[expose] public section

variable {R S : Type*} [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]

namespace RingEquiv

theorem toAlgHom_toRatAlgEquiv (f : R ≃+* S) :
    f.toRatAlgEquiv.toAlgHom = (f : R →+* S).toRatAlgHom :=
  rfl

end RingEquiv
end
