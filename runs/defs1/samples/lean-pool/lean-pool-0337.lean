@[expose] public section

open CategoryTheory AlgebraicTopology

noncomputable section

namespace SphereOddDegree

/-- A mod-two functional on `H₁(RPⁿ; F₂)` together with invariance under the
homology pushforward of every descended odd map. This is the interface used to
construct the degree-one class; `RPnMonodromyFunctional` supplies the canonical
instance. -/
structure MonodromyFunctional (n : ℕ) where
  /-- The `ZMod 2`-valued functional on `H₁(RPⁿ; F₂)`. -/
  g : homologyZMod2 (TopCat.of (RP n)) 1 →ₗ[ZMod 2] ZMod 2
  /-- Invariance under the homology pushforward of every descended odd map. -/
  invariant : ∀ (f : C(Sphere n, Sphere n)) (hf : IsOddMap f),
    g.comp (homologyPushZMod2 (TopCat.ofHom (inducedOnRP f hf)) 1).hom = g

end SphereOddDegree
end
end
