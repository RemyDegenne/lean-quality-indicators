@[expose] public section

universe u v

namespace RingHom

variable (p : ℕ) [Fact p.Prime] {R : Type u} {κ : Type v}
    [CommRing R] [CommRing κ] [CharP κ p] [PerfectRing κ p]
    (f : R →+* κ) (hf : Function.Surjective f) [IsAdicComplete (ker f) R]

theorem teichmullerSection_injective : Function.Injective (teichmullerSection p f hf) := by
  intro a b hab
  simpa only [teichmullerSection_reduction_apply] using congrArg f hab

end RingHom
end
