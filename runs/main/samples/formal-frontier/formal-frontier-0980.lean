@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

variable (R : Type u) [CommRing R] (n : ℕ)

theorem quotientMap_toRingHom :
    (quotientMap R n).toRingHom =
      Ideal.Quotient.lift (hankelIdeal R n) (rncMap R n)
        (fun p hp => RingHom.mem_ker.mp (hankelIdeal_le_ker R n hp)) := rfl

end ToricIdeals.RationalNormalCurve
end
