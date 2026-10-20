@[expose] public section

universe v₁ u₁ v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- The definition of a Grothendieck topology: a set of sieves `J X` on each object `X` satisfying
three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.

A sieve `S` on `X` is referred to as `J`-covering, (or just covering), if `S ∈ J X`.

See also [nlab] or [MM92] Chapter III, Section 2, Definition 1. -/
@[stacks 00Z4, wikidata Q1062242]
structure GrothendieckTopology where
  /-- A Grothendieck topology on `C` consists of a set of sieves for each object `X`,
  which satisfy some axioms. -/
  sieves : ∀ X : C, Set (Sieve X)
  /-- The sieves associated to each object must contain the top sieve.
  Use `GrothendieckTopology.top_mem`. -/
  top_mem' : ∀ X, ⊤ ∈ sieves X
  /-- Stability under pullback. Use `GrothendieckTopology.pullback_stable`. -/
  pullback_stable' : ∀ ⦃X Y : C⦄ ⦃S : Sieve X⦄ (f : Y ⟶ X), S ∈ sieves X → S.pullback f ∈ sieves Y
  /-- Transitivity of sieves in a Grothendieck topology. Use `GrothendieckTopology.transitive`. -/
  transitive' :
    ∀ ⦃X⦄ ⦃S : Sieve X⦄ (_ : S ∈ sieves X) (R : Sieve X),
      (∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ sieves Y) → R ∈ sieves X

end CategoryTheory
end
