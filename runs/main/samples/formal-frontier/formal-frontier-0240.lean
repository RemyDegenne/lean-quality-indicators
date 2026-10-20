@[expose] public section

universe uR uM uN uH uA uB

namespace MonoidAlgebra

variable {R : Type uR} {M : Type uM} {N : Type uN} {H : Type uH}

variable {A : Type uA} {B : Type uB}

section Bialgebra

variable [CommSemiring R] [Monoid M] [Semiring A] [Bialgebra R A]

theorem liftGroupLikeBialgHom_mapDomain_comp [Monoid N] (f : M →* GroupLike R A)
    (α : N →* M) :
    (liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R (f.comp α)) =
      ((liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R f)).comp
        (mapDomainBialgHom R α) := by
  apply (liftGroupLikeBialgHom_mapDomain_eq_iff (f.comp α) _).2
  intro n
  change ((liftGroupLikeBialgHom (R := R) (A := A)).comp
    (mapDomainBialgHom R f)) (mapDomainBialgHom R α (single n 1)) = (f (α n)).val
  rw [mapDomainBialgHom_single, liftGroupLikeBialgHom_mapDomain_single, one_smul]

end Bialgebra
end MonoidAlgebra
end
