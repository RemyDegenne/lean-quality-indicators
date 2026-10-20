@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace AlgebraicTopology

open Convexity Convexity.StdSimplex

universe u

theorem realize_subdivide_face_standard {X : TopCat.{u}} {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌) (i : Fin (n + 2)) :
    realizeAffineChain x n
        (subdivideSimplex n ((AffineSimplex.standard (n + 1)).face i)) =
      realizeAffineChain ((TopCat.toSSet.obj X).δ i x) n
        (subdivideSimplex n (AffineSimplex.standard n)) := by
  let f := (AffineSimplex.standard (n + 1)).face i
  have hsub := mapAffineChain_subdivideSimplex f (AffineSimplex.standard n)
  rw [AffineSimplex.comp_standard f] at hsub
  rw [← hsub]
  rw [realizeAffineChain_mapAffineChain]
  congr 2
  dsimp [f]
  rw [affinePostcompose_face, affinePostcompose_standard]

end AlgebraicTopology
end
end
