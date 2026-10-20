public section

open CategoryTheory Derivation

namespace TauCeti.CommHopfAlgCat.IsIsogeny

universe u

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}
  [Algebra.Smooth k H] [Algebra.Smooth k K] {f : H ⟶ K}

variable {M : Type u} [CommGroup M]

theorem dualCotangentMap_mem_adjointWeightSpace_iff (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (π : K →ₐc[k] MonoidAlgebra k M) (α : M)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    dualCotangentMap f.hom x ∈ adjointWeightSpace (π.comp f.hom) α ↔
      x ∈ adjointWeightSpace π α :=
  f.hom.dualCotangentMap_mem_adjointWeightSpace_iff_of_injective
    (hf.dualCotangentMap_bijective_of_etaleKernel hker).injective π α x

end TauCeti.CommHopfAlgCat.IsIsogeny
end
