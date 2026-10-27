@[expose] public section

namespace List

open Nat

universe u v w x

variable {α β γ δ ε ζ : Type*}

section Permutations

/-- List of all permutations of `l`. This version of `permutations` is less efficient but has
simpler definitional equations. The permutations are in a different order,
but are equal up to permutation, as shown by `List.permutations_perm_permutations'`.

```
     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 3, 2], [3, 1, 2], [3, 2, 1]]
```
-/
@[simp]
def permutations' : List α → List (List α)
  | [] => [[]]
  | t :: ts => (permutations' ts).flatMap <| permutations'Aux t

end Permutations
end List
end
