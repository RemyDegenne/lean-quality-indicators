@[expose] public section

noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

variable {ι : Type v}

namespace Pairwise

open Hom

/-- The identity morphism in `CategoryTheory.Pairwise ι`.
-/
def id : ∀ o : Pairwise ι, Hom o o
  | single i => id_single i
  | pair i j => id_pair i j

end Pairwise
end CategoryTheory
end
end
