public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TopPair

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  (P : TopPair.{w}) {ι : Type*} (U : ι → Set P.fst)

/-- The singular simplices of the ambient space of a topological pair whose image lies in a member
of the family `U`, as a subcomplex of the ambient simplicial set of the singular pair of `P`.  It is
`TopCat.smallSingularSubcomplex` of the ambient space, typed so that the singular pair can be
restricted to it. -/
def smallSingularSubcomplex : (toSSetPair.obj P).right.Subcomplex :=
  P.fst.smallSingularSubcomplex U

end TopPair
end
end
