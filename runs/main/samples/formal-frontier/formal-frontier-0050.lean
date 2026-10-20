@[expose] public section

universe a b c w p

open CategoryTheory

namespace SSet

variable {A : Type a} {B : Type b} {C : Type c}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

theorem tensorNormalizedChainComplexCoefficientMap_epi (g : A →+ B)
    (hSurj : Function.Surjective g) (S : SSet.{w}) :
    Epi (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S) := by
  apply HomologicalComplex.epi_of_epi_f
  intro n
  rw [tensorNormalizedChainComplexCoefficientMap_f]
  exact (ModuleCat.epi_iff_surjective _).2
    (tensorNormalizedCoefficientMap_surjective.{a, b, w, p} g hSurj S n)

end SSet
end
