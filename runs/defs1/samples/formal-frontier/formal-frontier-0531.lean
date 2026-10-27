set_option warningAsError true

public section

open CategoryTheory

universe u

attribute [instance] CompHausAddCommGrp.addCommGroup
  CompHausAddCommGrp.isTopologicalAddGroup

namespace CompHausAddCommGrp

/-- Morphisms of compact Hausdorff topological additive commutative groups. -/
@[ext]
structure Hom (A B : CompHausAddCommGrp.{u}) where
  /-- The underlying continuous additive homomorphism. -/
  hom' : A →ₜ+ B

end CompHausAddCommGrp
end
