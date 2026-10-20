@[expose] public section

open Algebra TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]

@[simp]
theorem PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply (q : PrimeSpectrum (p.Fiber S)) :
    (primesOverOrderIsoFiber R S p).symm q = q.1.comap Algebra.TensorProduct.includeRight :=
  rfl

end
