@[expose] public section

open CategoryTheory Limits Opposite Functor

open scoped Simplicial

universe w v u vD uD

namespace CategoryTheory.Limits.Types

/-- The equivalence between fibers supplied by a pullback square. -/
noncomputable def pullbackFiberEquiv {A B U V : Type w} {t : A ⟶ B} {l : A ⟶ U}
    {r : B ⟶ V} {b : U ⟶ V} (h : IsPullback t l r b) (x : U) :
    {a : A // l a = x} ≃ {y : B // r y = b x} :=
  Equiv.ofBijective _ (pullbackFiberMap_bijective h x)

end CategoryTheory.Limits.Types
end
