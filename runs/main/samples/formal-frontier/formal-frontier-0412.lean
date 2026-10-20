@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

theorem affineBoundaryHom_eq (m n : ℕ) :
    affineBoundaryHom m n = ModuleCat.ofHom (affineBoundary m n) := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro a
  apply LinearMap.ext
  intro z
  exact congrArg (fun f ↦ f z) (lsingle_comp_affineBoundaryHom a |>.trans
    (lsingle_comp_affineBoundary a).symm)

end Convexity.StdSimplex
end
end
