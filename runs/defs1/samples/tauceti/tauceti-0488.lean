public section

open CategoryTheory

open scoped DirectSum

namespace Homotopy

open CochainComplex

universe u v

variable {R : Type u} [Ring R] {K L : CochainComplex (ModuleCat.{v} R) ℕ} {f g : K ⟶ L}

/-- The total map of a homotopy between cochain morphisms: it lowers the summand index by one,
applying the component `H.hom (n + 1) n` to the degree-`n + 1` summand, and vanishes on the
degree-zero summand. -/
def directSumHomotopy (H : Homotopy f g) : K.directSumModule →ₗ[R] L.directSumModule :=
  DirectSum.toModule R ℕ _ fun
    | 0 => 0
    | n + 1 => (DirectSum.lof R ℕ (fun n ↦ L.X n) n).comp (H.hom (n + 1) n).hom

end Homotopy
end
