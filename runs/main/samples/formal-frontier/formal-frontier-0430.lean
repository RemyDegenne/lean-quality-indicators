@[expose] public section

universe u v

namespace RingHom.IsIntegral

theorem ringKrullDim_eq_quotient_ker {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.IsIntegral) :
    ringKrullDim S = ringKrullDim (R ⧸ RingHom.ker f) := by
  exact (hf.kerLift.ringKrullDim_eq (RingHom.kerLift_injective f)).symm

end RingHom.IsIntegral
end
