public section

namespace TauCeti.ValuationSpectrum

open _root_.TopologicalSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A]

open scoped Classical in
@[simp]
theorem rationalSubset_insert_self (Aplus : Subring A) (T : Finset A) (s : A) :
    rationalSubset Aplus (insert s T) s = rationalSubset Aplus T s := by
  rw [rationalSubset_def, rationalSubset_def, basicOpenFinset_insert_self]

end TauCeti.ValuationSpectrum
end
