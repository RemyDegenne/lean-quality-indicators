public section

open scoped Pointwise

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}

variable [Field k] [Field F] [Field F'] [Algebra k F'] [Algebra F F']

section Galois

variable (F) [Algebra k F] [IsScalarTower k F F'] [FiniteDimensional F F'] [IsGalois F F']
  (P : Place k F')

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- **The decomposition group modulo the inertia group is the automorphism group of the residue
extension** (Stichtenoth, Theorem 3.8.2). -/
noncomputable def decompositionQuotientInertiaEquiv :
    P.integers.decompositionSubgroup F ⧸ P.integers.inertiaSubgroup F ≃*
      (P.ResidueField ≃ₐ[(P.restrict k F).ResidueField] P.ResidueField) :=
  QuotientGroup.liftEquiv _ (residueAut_surjective F P) (ker_residueAut F P).symm

end Galois
end Place
end TauCeti
end
