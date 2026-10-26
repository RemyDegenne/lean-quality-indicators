/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# Coalgebras on idempotent principal ideals

For an idempotent `e` in a commutative semiring `K`, `IsIdempotentElem.coalgebraSpan`
equips the existing ideal `Ideal.span {e}` with counit the scalar inclusion and
comultiplication `d ↦ d ⊗ e`. The idempotent acts as the identity on this ideal,
and every member `d` is its scalar value times the generator.

The construction is an explicit definition, not a global instance. Install it
locally with `letI := he.coalgebraSpan`. Its characteristic comultiplication and
counit lemmas apply to that coalgebra structure. No freeness, domain or
Noetherian hypothesis is required, and zero and one are allowed as generators.

## References

The ideal carrier and principal-ideal membership API, and the tensor-product
and coalgebra APIs, are supplied by Mathlib.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open scoped TensorProduct

namespace Ideal

variable {K : Type u} [Semiring K]

/-- The specified generator as a member of its principal ideal. -/
def spanSingletonGenerator (e : K) : Ideal.span ({e} : Set K) :=
  ⟨e, Ideal.mem_span_singleton_self e⟩

@[simp] theorem coe_spanSingletonGenerator (e : K) :
    (spanSingletonGenerator e : K) = e := rfl

end Ideal

namespace IsIdempotentElem

variable {K : Type u} [CommSemiring K] {e : K}

/-- An idempotent acts as the identity on its principal ideal. -/
theorem smul_span_singleton (he : IsIdempotentElem e)
    (d : Ideal.span ({e} : Set K)) : e • d = d := by
  apply Subtype.ext
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp d.property
  change e * (d : K) = (d : K)
  rw [← hr, mul_left_comm e r e, he.eq]

/-- The scalar value of a member of an idempotent ideal is its coefficient
with respect to the specified generator. -/
theorem smul_spanSingletonGenerator (he : IsIdempotentElem e)
    (d : Ideal.span ({e} : Set K)) : (d : K) • Ideal.spanSingletonGenerator e = d := by
  apply Subtype.ext
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp d.property
  change (d : K) * e = (d : K)
  rw [← hr, mul_assoc, he.eq]

/-- The coalgebra on the principal ideal of an idempotent, with counit inclusion
and comultiplication `d ↦ d ⊗ e`. -/
@[instance_reducible]
noncomputable def coalgebraSpan (he : IsIdempotentElem e) :
    Coalgebra K (Ideal.span ({e} : Set K)) where
  comul := (TensorProduct.mk K _ _).flip (Ideal.spanSingletonGenerator e)
  counit := (Ideal.span ({e} : Set K)).subtype
  coassoc := by
    ext d
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.assoc_tmul,
      LinearEquiv.coe_coe]
  rTensor_counit_comp_comul := by
    ext d
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.rTensor_tmul, Submodule.coe_subtype]
    calc
      (d : K) ⊗ₜ[K] Ideal.spanSingletonGenerator e =
          (d : K) • ((1 : K) ⊗ₜ[K] Ideal.spanSingletonGenerator e) := by
        rw [TensorProduct.smul_tmul']
        simp
      _ = (1 : K) ⊗ₜ[K] ((d : K) • Ideal.spanSingletonGenerator e) :=
        (TensorProduct.tmul_smul _ _ _).symm
      _ = (1 : K) ⊗ₜ[K] d := by rw [he.smul_spanSingletonGenerator d]
  lTensor_counit_comp_comul := by
    ext d
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.lTensor_tmul, Submodule.coe_subtype, Ideal.coe_spanSingletonGenerator]
    calc
      d ⊗ₜ[K] e = e • (d ⊗ₜ[K] (1 : K)) := by
        rw [← TensorProduct.tmul_smul]
        simp
      _ = (e • d) ⊗ₜ[K] (1 : K) := TensorProduct.smul_tmul' _ _ _
      _ = d ⊗ₜ[K] (1 : K) := by rw [he.smul_span_singleton d]

/-- Comultiplication on a member of an idempotent principal ideal. -/
@[simp] theorem coalgebraSpan_comul_apply (he : IsIdempotentElem e)
    (d : Ideal.span ({e} : Set K)) :
    he.coalgebraSpan.comul d = d ⊗ₜ[K] Ideal.spanSingletonGenerator e := rfl

/-- The counit linear map is the inclusion into the scalars. -/
theorem coalgebraSpan_counit (he : IsIdempotentElem e) :
    he.coalgebraSpan.counit = (Ideal.span ({e} : Set K)).subtype := rfl

/-- The counit of a member of an idempotent principal ideal. -/
@[simp] theorem coalgebraSpan_counit_apply (he : IsIdempotentElem e)
    (d : Ideal.span ({e} : Set K)) : he.coalgebraSpan.counit d = (d : K) := rfl

/-- The generator has diagonal comultiplication; its counit is the scalar `e`,
which need not be one. -/
theorem coalgebraSpan_comul_generator (he : IsIdempotentElem e) :
    he.coalgebraSpan.comul (Ideal.spanSingletonGenerator e) =
      Ideal.spanSingletonGenerator e ⊗ₜ[K] Ideal.spanSingletonGenerator e := rfl

end IsIdempotentElem
