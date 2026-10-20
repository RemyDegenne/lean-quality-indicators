public section

open CategoryTheory

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace FGComoduleCat

variable (R : Type u) (C : Type v)

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable {M : Type w} [AddCommMonoid M] [Module R M] [Module.Finite R (M ⊗[R] C)]

variable {N : Type w} [AddCommMonoid N] [Module R N] [Module.Finite R (N ⊗[R] C)]

attribute [local instance] Comodule.cofree

/-- The cofree right `C`-comodule with finitely generated tensor-product carrier, bundled as an
object of `FGComoduleCat`.

The underlying module is `M ⊗[R] C`, with coaction `id ⊗ Δ` followed by reassociation. -/
noncomputable abbrev cofree (M : Type w) [AddCommMonoid M] [Module R M]
    [Module.Finite R (M ⊗[R] C)] : FGComoduleCat.{u, v, max w v} R C :=
  of (R := R) (C := C) (M ⊗[R] C)

end FGComoduleCat
end TauCeti
end
