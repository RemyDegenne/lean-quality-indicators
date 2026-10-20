public section

universe u

open CategoryTheory Simplicial

namespace SSet

namespace KanComplex

/-- The `n`th homotopy group of a simplicial set `X` at a vertex `x`: the homotopy classes,
relative to the boundary `∂Δ[n]`, of morphisms `Δ[n] ⟶ X` sending `∂Δ[n]` to `x`. It is a group
for `n ≥ 1` when `X` is a Kan complex (`SSet.KanComplex.π.group`). -/
def π (n : ℕ) (X : SSet.{u}) (x : X _⦋0⦌) : Type u :=
  RelativeMorphism.HomotopyClass ∂Δ[n] (Subcomplex.ofSimplex x)
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

end KanComplex
end SSet
end
