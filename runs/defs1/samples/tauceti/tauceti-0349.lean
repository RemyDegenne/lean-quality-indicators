public section

open CategoryTheory

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace FGComoduleCat

variable (R : Type u) [CommSemiring R]

variable (C : Type v) [Semiring C] [Bialgebra R C]

attribute [local instance] Comodule.tensor

variable {R C}

variable {M M' M'' N N' N'' : FGComoduleCat.{u, v, w} R C}

variable (R C)

/-- Tensor product as a bifunctor on finitely generated right comodules.

It sends `(M, N)` to the finite diagonal comodule `M ⊗ N` and a pair of morphisms `(f, g)`
to `f ⊗ g`. This is the tensor bifunctor underlying the future monoidal structure on
`FGComoduleCat`. -/
@[expose]
noncomputable def tensorBifunctor :
    FGComoduleCat.{u, v, w} R C × FGComoduleCat.{u, v, w} R C ⥤
      FGComoduleCat.{u, v, w} R C where
  obj P := tensor R C P.1 P.2
  map fg := tensorMap fg.1 fg.2
  map_id P := tensorMap_id P.1 P.2
  map_comp f g := tensorMap_comp f.1 g.1 f.2 g.2

end FGComoduleCat
end TauCeti
end
