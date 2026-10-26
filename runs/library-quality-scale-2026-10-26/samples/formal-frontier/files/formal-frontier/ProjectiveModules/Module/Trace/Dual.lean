/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.Basic

/-!
# Trace of a dual endomorphism

Taking the dual of an endomorphism preserves its finite-projective trace over a
commutative semiring. The dual endomorphism acts on linear forms by
precomposition, and the dual module has its pointwise scalar action.

## References

The dual and evaluation pairing are formalized by Johan Commelin, Fabian Glöckle
and Kyle Miller in `Mathlib.LinearAlgebra.Dual.Defs`. The tensor–Hom transpose
formula and contraction pairing are formalized by Oliver Nash and Antoine
Labelle in `Mathlib.LinearAlgebra.Contraction`.
-/

@[expose] public section

universe uR uM

namespace LinearMap

/-- The finite-projective trace of an endomorphism equals the trace of its dual
endomorphism, which acts on linear forms by precomposition. The tensor–Hom
transpose formula is from the formalization by Oliver Nash and Antoine Labelle
in `Mathlib.LinearAlgebra.Contraction`. -/
theorem traceOfFiniteProjective_dualMap
    (R : Type uR) (M : Type uM)
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (f : M →ₗ[R] M) :
    traceOfFiniteProjective R (Module.Dual R M) f.dualMap =
      traceOfFiniteProjective R M f := by
  rw [dualMap_def]
  have h (t : TensorProduct R (Module.Dual R M) M) :
      traceOfFiniteProjective R (Module.Dual R M)
          (Module.Dual.transpose (dualTensorHom R M M t)) =
        traceOfFiniteProjective R M (dualTensorHom R M M t) := by
    induction t using TensorProduct.inductionOn with
    | tmul φ x =>
      simp only [transpose_dualTensorHom, traceOfFiniteProjective_dualTensorHom,
        contractLeft_apply, Module.Dual.eval_apply]
    | add t s ht hs =>
      simp only [map_add, ht, hs]
  simpa only [dualTensorHom_dualTensorHomEquiv_symm] using
    h ((dualTensorHomEquiv R M M).symm f)

end LinearMap
