public section

namespace RingEquiv

variable {R S : Type*}

theorem isCatenary [CommSemiring R] [CommSemiring S] [TauCeti.Excellence.IsCatenary R]
    (e : R ≃+* S) : TauCeti.Excellence.IsCatenary S :=
  (PrimeSpectrum.comapEquiv e).symm.isCatenary

end RingEquiv
end
