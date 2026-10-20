@[expose] public section

universe u v

namespace RingHom

variable (p : ℕ) [Fact p.Prime] {R : Type u} {κ : Type v}
    [CommRing R] [CommRing κ] [CharP κ p] [PerfectRing κ p]
    (f : R →+* κ) (hf : Function.Surjective f) [IsAdicComplete (ker f) R]

@[simp]
theorem teichmullerSection_reduction_apply (a : κ) :
    f (teichmullerSection p f hf a) = a := by
  let e := f.quotientKerEquivOfSurjective hf
  let : CharP (R ⧸ ker f) p :=
    charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  rw [teichmullerSection_eq_comp]
  change e (Ideal.Quotient.mk (ker f)
    (Perfection.teichmuller₀ p (ker f)
      ((Perfection.lift p κ (R ⧸ ker f)) e.symm.toRingHom a))) = a
  rw [Perfection.mk_teichmuller₀, Perfection.coeff_lift]
  exact e.apply_symm_apply a

end RingHom
end
