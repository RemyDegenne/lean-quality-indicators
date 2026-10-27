set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

universe u v w

open CategoryTheory TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (X : TopRep.{max v w} k G)

/-- Continuous, equivariant inclusion of the coarser invariant coefficients
into the finer ones, viewed as a morphism of `G ⧸ N`-representations. -/
def quotientTransitionIncl {N M : OpenNormalSubgroup G} (hNM : N ≤ M) :
    TopRep.res (quotientTransitionHom N M hNM)
      (TopRep.quotientInvariants M.toSubgroup X) ⟶
        TopRep.quotientInvariants N.toSubgroup X :=
  TopRep.ofHom {
    toContinuousLinearMap :=
      ((X.ρ.restrict M.toSubgroup.subtype).invariants).subtypeL.codRestrict
        ((X.ρ.restrict N.toSubgroup.subtype).invariants)
        (fun x t => x.2 ⟨t.1, hNM t.2⟩)
    isIntertwining' := by
      intro q
      induction q using QuotientGroup.induction_on with
      | _ g =>
        ext x
        change X.ρ g x.1 = X.ρ g x.1
        rfl
  }

end ContinuousCohomology
end
