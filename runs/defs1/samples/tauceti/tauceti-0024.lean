public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι} {V : Finset ι}
  {n : ℕ} {v w : ι}

/-- `K` is a **combinatorial `n`-manifold** when the link of each of its vertices is a
combinatorial `(n-1)`-sphere (an interior vertex) or a combinatorial `(n-1)`-ball (a boundary
vertex).

The dimension is matched against rather than decremented: in dimension `0` the condition is that
every vertex has void link, which is what a discrete set of points satisfies, and which no
combinatorial ball or sphere does. -/
def IsCombinatorialManifold (K : PreAbstractSimplicialComplex ι) : ℕ → Prop
  | 0 => ∀ ⦃v : ι⦄, ({v} : Finset ι) ∈ K → link K {v} = ⊥
  | n + 1 => ∀ ⦃v : ι⦄, ({v} : Finset ι) ∈ K →
      IsCombinatorialSphere (link K {v}) n ∨ IsCombinatorialBall (link K {v}) n

end PreAbstractSimplicialComplex
end
