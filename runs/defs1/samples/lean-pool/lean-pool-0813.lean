@[expose] public section

namespace LeanPool.KrohnRhodes

universe u

open Green

attribute [instance] KRFactor.mon KRFactor.fin

/-- **The recursive division predicate of a factor tower.**

    `DivTowerWreath M factors` records the following recursive wreath divisions:

    * `[]`           — `M` divides the trivial monoid `PUnit` (the empty product;
                       this forces `M` to be a single point up to division).
    * `F :: rest`    — there is a finite base monoid `B` that itself decomposes
                       via the *tail* `rest` (`DivTowerWreath B rest`), and `M`
                       divides `WreathProduct F.carrier B Y` for some finite type
                       `Y` on which `B` acts: the head factor `F.carrier` sits in
                       the decoration slot over the base `B`.

    No action-lifting or equivalence with a single iterated transformation wreath product
    is asserted by this definition. The intermediate base at each step has its own tower. -/
def DivTowerWreath : (M : Type u) → [Monoid M] → [Finite M] → List KRFactor.{u} → Prop
  | M, _, _, [] => SgDiv M PUnit.{u + 1}
  | M, _, _, (F :: rest) =>
      ∃ (B : Type u) (_ : Monoid B) (_ : Finite B)
        (Y : Type u) (_ : Fintype Y) (_ : MulAction B Y),
        DivTowerWreath B rest ∧
        SgDiv M (WreathProduct F.carrier B Y)

end LeanPool.KrohnRhodes
end
