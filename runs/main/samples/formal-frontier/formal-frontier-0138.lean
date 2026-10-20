@[expose] public section

noncomputable section

open CategoryTheory

namespace MvPolynomial

universe u

variable {K : Type u} [Field K] {σ : Type u}

@[simp] theorem zeroLocusSchemePoint_val (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) :
    (zeroLocusSchemePoint I a).val = AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (zeroLocusQuotientEval I a).toRingHom) := rfl

end MvPolynomial
end
end
