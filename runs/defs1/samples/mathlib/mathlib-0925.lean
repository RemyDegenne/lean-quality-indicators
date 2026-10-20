@[expose] public section

open CategoryTheory Category Limits CochainComplex.HomComplex Pretriangulated

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

namespace CochainComplex

namespace mappingCone

variable (K) in
/-- The mapping cone of the identity is contractible. -/
noncomputable def homotopyToZeroOfId : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 :=
  descHomotopy (𝟙 K) _ _ 0 (inl _) (by simp) (by simp)

end mappingCone
end CochainComplex
end
