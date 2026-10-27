public section

open CategoryTheory Limits

universe v u

namespace TauCeti

namespace PeriodicComplex

variable {C : Type u} [Category.{v} C]

section Homotopy

variable [Preadditive C] (n : ℕ)

variable {K L M : CochainComplex C ℤ} [HasCompression n K] [HasCompression n L]
  [HasCompression n M]

/-- The isomorphism of compressions induced by an isomorphism in the homotopy category. -/
noncomputable def quotientCompressionIso
    (e : (HomotopyCategory.quotient C _).obj K ≅ (HomotopyCategory.quotient C _).obj L) :
    (HomotopyCategory.quotient C _).obj (compression n K) ≅
      (HomotopyCategory.quotient C _).obj (compression n L) where
  hom := quotientCompressionMap n e.hom
  inv := quotientCompressionMap n e.inv
  hom_inv_id := by rw [← quotientCompressionMap_comp, e.hom_inv_id, quotientCompressionMap_id]
  inv_hom_id := by rw [← quotientCompressionMap_comp, e.inv_hom_id, quotientCompressionMap_id]

end Homotopy
end PeriodicComplex
end TauCeti
end
