@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

theorem AffineSimplex.comp_face {m n k : ℕ} (a : AffineSimplex m n)
    (b : AffineSimplex n (k + 1)) (i : Fin (k + 2)) :
    (a.comp b).face i = a.comp (b.face i) := rfl

end Convexity.StdSimplex
end
end
