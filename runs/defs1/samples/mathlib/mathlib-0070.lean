@[expose] public section

open List (Vector)

open Function (update)

open Relation StateTransition

namespace Turing

namespace PartrecToTM2

section

open ToPartrec

open K'

open TM2.Stmt

/-- Assuming `trList v` is on the front of stack `k`, remove it, and push `v.headI` onto `main`.
See the section documentation. -/
def head (k : K') (q : Λ') : Λ' :=
  Λ'.move natEnd k rev <|
    (Λ'.push rev fun _ => some Γ'.cons) <|
      Λ'.read fun s =>
        (if s = some Γ'.consₗ then id else Λ'.clear (fun x => x = Γ'.consₗ) k) <| unrev q

end
end PartrecToTM2
end Turing
end
