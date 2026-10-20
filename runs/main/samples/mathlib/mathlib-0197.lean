@[expose] public section

universe w u v

namespace TopRep

variable {k : Type u} {G : Type v} {X Y : Type w} [TopologicalSpace k] [Ring k]
  [Monoid G] [AddCommGroup X] [Module k X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul k X] [AddCommGroup Y] [Module k Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul k Y] {ρ : ContRepresentation k G X}
  {σ : ContRepresentation k G Y}

open ContRepresentation CategoryTheory

attribute [instance] hV1 hV2 hV3 hV4 hV5

variable (A B C : TopRep.{w} k G)

section Linear

variable {k : Type u} {G : Type v} {X Y : Type w} [TopologicalSpace k] [CommRing k]
  [Monoid G] [AddCommGroup X] [Module k X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul k X] [AddCommGroup Y] [Module k Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul k Y] {ρ : ContRepresentation k G X}
  {σ : ContRepresentation k G Y} {A B C : TopRep k G}

variable (A B C) in
lemma comp_smul' (f : A ⟶ B) (r : k) (g : B ⟶ C) : f ≫ (r • g) = r • (f ≫ g) := by
  ext; simp [hom_smul, ContIntertwiningMap.smul_comp]

end Linear
end TopRep
end
