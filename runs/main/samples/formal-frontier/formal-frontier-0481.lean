@[expose] public section

open CategoryTheory Limits Opposite

open scoped Simplicial

universe w v u

namespace IsCoveringMap

variable {X Y : TopCat.{w}} {p : Y ⟶ X}

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

theorem singularChainComplexTransfer_f (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (n : ℕ) :
    (hp.singularChainComplexTransfer hf R).f n =
      sigmaConstTransfer ((TopCat.toSSet.map p).app (op ⦋n⦌))
        (fun s => by
          let := hf (X.toSSetObjEquiv (op ⦋n⦌) s default)
          exact hp.finite_singularLift (op ⦋n⦌) s default) R :=
  rfl

end IsCoveringMap
end
