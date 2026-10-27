set_option warningAsError true

@[expose] public section

universe u v w

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] (N : Subgroup G) [N.Normal]

/-- Map invariants of equivariant continuous linear maps, preserving the residual quotient
action. -/
def quotientInvariantsMap {X Y : TopRep.{w} k G} (f : X ⟶ Y) :
    quotientInvariants N X ⟶ quotientInvariants N Y :=
  ofHom {
    toContinuousLinearMap := (f.hom.restrict N.subtype).mapInvariants
    isIntertwining' := by
      intro q
      induction q using QuotientGroup.induction_on with
      | _ g =>
        ext x
        change f.hom (X.ρ g x.1) = Y.ρ g (f.hom x.1)
        exact f.hom.isIntertwining g x.1
  }

end TopRep
end
