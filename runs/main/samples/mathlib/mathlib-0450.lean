@[expose] public section

open CategoryTheory Abelian Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace CochainComplex

lemma degreewiseEpiWithInjectiveKernel_iff_of_isZero {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (hL : IsZero L) :
    degreewiseEpiWithInjectiveKernel f ↔ ∀ (n : ℤ), Injective (K.X n) :=
  forall_congr' (fun n ↦ by
    rw [epiWithInjectiveKernel_iff_of_isZero]
    exact (HomologicalComplex.eval _ _ n).map_isZero hL)

end CochainComplex
end
