public section

open scoped Matrix

universe v

namespace TauCeti.E6Minuscule

open AlgebraicGeometry CategoryTheory

open TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra

open scoped CategoryTheory.MonObj TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

local notation "CM" => weightTable.cartanMatrix

local notation "rootGen" => TauCeti.serreRootGenerator CM

local notation "cartanGen" => TauCeti.serreH ℚ CM

local notation "rootWeight" => TauCeti.E6.rootGeneratorWeight

local notation "rootWeight6" =>
  (fun k : Fin 6 ⊕ Fin 6 => fun j : Fin 6 => rootWeight k j)

local notation "Λ" => TauCeti.coordinateLattice (Fin 27)

local notation "𝓑" => TauCeti.coordinateLatticeBasis (Fin 27)

/-- The `i`-th positive simple-root subgroup factored through the positive subsystem. -/
noncomputable def positiveRootSubgroup (i : Fin 6) :
    AdditiveGroup.groupScheme ℤ ⟶ positiveSubsystemGroupScheme :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToTorusSubsystem rootGen cartanGen
    weightTable.rep
    (Λ).toAddSubgroup weightTable.rep_kostantForm_mem_lattice 𝓑 weightTable.weight
    positiveSimpleRoots (fun k => weightTable.isNilpotent_rep_serreRootGenerator k.1)
    (inl_mem_positiveSimpleRoots i) ≫ eqToHom positiveSubsystemGroupScheme_def.symm

end TauCeti.E6Minuscule
end
