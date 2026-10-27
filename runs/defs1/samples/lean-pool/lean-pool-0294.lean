@[expose] public section

noncomputable section

open Finset

namespace CategoryTheory.Dilatations

section RingDilatation

variable {ι A' B' F' : Type*} [CommSemiring A'] [CommSemiring B'] [FunLike F' A' B']
  [RingHomClass F' A' B']

scoped[CategoryTheory.Dilatations.Family] attribute [instance]
  CategoryTheory.Dilatations.instFamilyPow

open DirectSum Family

namespace Multicenter

section universal_property

variable {A' B' : Type*} [CommRing A'] [CommRing B'] (M : Multicenter A')

/-- The unique quotient of a mapped numerator by its mapped denominator. -/
def fractionValue [Algebra A' B'] (v : M^ℕ) (m : M.LargeIdeal ^ v)
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B')
      (M.LargeIdeal i)): B' :=
     (lemma_exists_in_image M non_zero_divisor gen v m).choose

end universal_property
end Multicenter
end RingDilatation
end CategoryTheory.Dilatations
end
end
