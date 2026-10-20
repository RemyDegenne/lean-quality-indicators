public section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat R) c) (n : ι)

section HomologyClass

variable {n} {m : ι} (hm : c.next n = m) {Z : Type*} [AddCommGroup Z] [Module R Z]
  (j : Z →ₗ[R] K.X n) (hj : ∀ z, K.d n m (j z) = 0)

lemma moduleCatHomologyClass_eq_zero_iff {p : ι} (hp : c.prev n = p) (z : Z) :
    K.moduleCatHomologyClass hm j hj z = 0 ↔ ∃ y : K.X p, K.d p n y = j z := by
  rw [moduleCatHomologyClass_apply, K.moduleCat_homologyπ_eq_zero_iff hp]
  refine exists_congr fun y ↦ ?_
  rw [← (K.moduleCat_iCycles_injective n).eq_iff, iCycles_moduleCatCyclesMk,
    ← ModuleCat.comp_apply, toCycles_i]

end HomologyClass
end HomologicalComplex
end
